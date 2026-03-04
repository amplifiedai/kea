use crossbeam_deque::{Injector, Steal, Stealer, Worker};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{mpsc, Arc, Condvar, Mutex};
use std::thread::{self, JoinHandle};
use std::time::Duration;

/// Scheduler hint derived from a task's effect row.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EffectHint {
    /// Pure CPU-bound task (`->`).
    Pure,
    /// Task may block on IO (`-[IO]>`).
    Io,
    /// Task may interact with concurrency/runtime effects.
    Concurrent,
}

trait Runnable {
    fn run(self: Box<Self>);
}

impl<F> Runnable for F
where
    F: FnOnce(),
{
    fn run(self: Box<Self>) {
        (*self)();
    }
}

type Job = Box<dyn Runnable + Send + 'static>;

struct JobEnvelope {
    hint: EffectHint,
    job: Job,
}

impl JobEnvelope {
    fn new(hint: EffectHint, job: Job) -> Self {
        Self { hint, job }
    }

    fn run(self) {
        // V1: hint is plumbed through scheduling data structures but not yet
        // lane-specialized. That policy lands in the next runtime slice.
        let _hint = self.hint;
        self.job.run();
    }
}

struct ParkState {
    mutex: Mutex<()>,
    cv: Condvar,
}

impl ParkState {
    fn new() -> Self {
        Self {
            mutex: Mutex::new(()),
            cv: Condvar::new(),
        }
    }

    fn wake_one(&self) {
        self.cv.notify_one();
    }

    fn wake_all(&self) {
        self.cv.notify_all();
    }
}

struct RuntimeInner {
    injector: Injector<JobEnvelope>,
    park: ParkState,
    shutdown: AtomicBool,
    stealers: Arc<Vec<Stealer<JobEnvelope>>>,
}

impl RuntimeInner {
    fn enqueue(&self, job: JobEnvelope) {
        self.injector.push(job);
        self.park.wake_one();
    }
}

/// Join handle for a submitted task.
pub struct TaskHandle<T> {
    rx: mpsc::Receiver<T>,
}

impl<T> TaskHandle<T> {
    /// Block until the task completes.
    pub fn join(self) -> T {
        self.rx
            .recv()
            .expect("task worker exited before sending result")
    }
}

/// Work-stealing runtime used by `Par` lowering.
///
/// Architecture: per-worker Chase-Lev deques plus a shared injector queue.
pub struct Runtime {
    inner: Arc<RuntimeInner>,
    workers: Vec<JoinHandle<()>>,
}

impl Runtime {
    /// Create a runtime with `threads` worker threads.
    pub fn new(threads: usize) -> Self {
        assert!(threads > 0, "runtime requires at least one worker thread");

        let mut local_queues = Vec::with_capacity(threads);
        let mut stealers = Vec::with_capacity(threads);
        for _ in 0..threads {
            let local = Worker::new_fifo();
            stealers.push(local.stealer());
            local_queues.push(local);
        }

        let stealers = Arc::new(stealers);
        let inner = Arc::new(RuntimeInner {
            injector: Injector::new(),
            park: ParkState::new(),
            shutdown: AtomicBool::new(false),
            stealers: stealers.clone(),
        });

        let mut workers = Vec::with_capacity(threads);
        for (worker_id, local) in local_queues.into_iter().enumerate() {
            let inner_cloned = inner.clone();
            workers.push(
                thread::Builder::new()
                    .name(format!("kea-runtime-worker-{worker_id}"))
                    .spawn(move || worker_loop(worker_id, local, inner_cloned))
                    .expect("failed to spawn runtime worker"),
            );
        }

        Self { inner, workers }
    }

    /// Number of runtime worker threads.
    pub fn threads(&self) -> usize {
        self.workers.len()
    }

    /// Submit a task and return a handle for its result.
    pub fn spawn_with_hint<F, T>(&self, hint: EffectHint, f: F) -> TaskHandle<T>
    where
        F: FnOnce() -> T + Send + 'static,
        T: Send + 'static,
    {
        let (tx, rx) = mpsc::sync_channel(1);
        let job = JobEnvelope::new(
            hint,
            Box::new(move || {
                let _ = tx.send(f());
            }),
        );
        self.inner.enqueue(job);
        TaskHandle { rx }
    }

    /// Convenience API for pure tasks.
    pub fn spawn<F, T>(&self, f: F) -> TaskHandle<T>
    where
        F: FnOnce() -> T + Send + 'static,
        T: Send + 'static,
    {
        self.spawn_with_hint(EffectHint::Pure, f)
    }

    /// Parallel map that preserves input ordering.
    pub fn parallel_map<T, U, F>(&self, items: Vec<T>, f: F) -> Vec<U>
    where
        T: Send + 'static,
        U: Send + 'static,
        F: Fn(T) -> U + Send + Sync + 'static,
    {
        let mapper = Arc::new(f);
        let mut handles = Vec::with_capacity(items.len());

        for (index, item) in items.into_iter().enumerate() {
            let mapper_cloned = mapper.clone();
            handles.push(self.spawn(move || (index, mapper_cloned(item))));
        }

        let mut out: Vec<Option<U>> = (0..handles.len()).map(|_| None).collect();
        for handle in handles {
            let (index, value) = handle.join();
            out[index] = Some(value);
        }

        out.into_iter()
            .map(|slot| slot.expect("parallel map slot missing result"))
            .collect()
    }
}

impl Drop for Runtime {
    fn drop(&mut self) {
        self.inner.shutdown.store(true, Ordering::Release);
        self.inner.park.wake_all();

        for worker in self.workers.drain(..) {
            let _ = worker.join();
        }
    }
}

fn try_pop_work(
    local: &Worker<JobEnvelope>,
    inner: &RuntimeInner,
    worker_id: usize,
) -> Option<JobEnvelope> {
    if let Some(local_job) = local.pop() {
        return Some(local_job);
    }

    match inner.injector.steal_batch_and_pop(local) {
        Steal::Success(job) => return Some(job),
        Steal::Retry | Steal::Empty => {}
    }

    for (idx, stealer) in inner.stealers.iter().enumerate() {
        if idx == worker_id {
            continue;
        }
        match stealer.steal_batch_and_pop(local) {
            Steal::Success(job) => return Some(job),
            Steal::Retry | Steal::Empty => {}
        }
    }

    None
}

fn worker_loop(worker_id: usize, local: Worker<JobEnvelope>, inner: Arc<RuntimeInner>) {
    loop {
        if let Some(job) = try_pop_work(&local, &inner, worker_id) {
            job.run();
            continue;
        }

        if inner.shutdown.load(Ordering::Acquire) && inner.injector.is_empty() && local.is_empty() {
            break;
        }

        let guard = inner.park.mutex.lock().expect("park mutex poisoned");
        let _ = inner
            .park
            .cv
            .wait_timeout(guard, Duration::from_millis(2))
            .expect("park condvar poisoned");
    }
}

#[cfg(test)]
mod tests {
    use super::{EffectHint, Runtime};
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;
    use std::time::Duration;

    #[test]
    fn executes_spawned_tasks() {
        let runtime = Runtime::new(4);
        let counter = Arc::new(AtomicUsize::new(0));

        let handles = (0..1000)
            .map(|_| {
                let counter = counter.clone();
                runtime.spawn_with_hint(EffectHint::Pure, move || {
                    counter.fetch_add(1, Ordering::Relaxed);
                })
            })
            .collect::<Vec<_>>();

        for handle in handles {
            handle.join();
        }

        assert_eq!(counter.load(Ordering::Relaxed), 1000);
    }

    #[test]
    fn parallel_map_preserves_order() {
        let runtime = Runtime::new(4);
        let input = (0..512).collect::<Vec<i64>>();
        let output = runtime.parallel_map(input.clone(), |x| x * 3);

        assert_eq!(output.len(), input.len());
        for (idx, value) in output.into_iter().enumerate() {
            assert_eq!(value, input[idx] * 3);
        }
    }

    #[test]
    fn parallel_map_handles_skewed_tasks() {
        let runtime = Runtime::new(4);
        let input = (0..128).collect::<Vec<u32>>();
        let output = runtime.parallel_map(input.clone(), |x| {
            if x % 17 == 0 {
                std::thread::sleep(Duration::from_millis(2));
            }
            x + 1
        });

        assert_eq!(output.len(), input.len());
        for (idx, value) in output.into_iter().enumerate() {
            assert_eq!(value, input[idx] + 1);
        }
    }

    #[test]
    fn drop_waits_for_queued_tasks() {
        let runtime = Runtime::new(2);
        let handles = (0..64)
            .map(|x| runtime.spawn(move || x * x))
            .collect::<Vec<_>>();

        drop(runtime);

        let mut values = handles.into_iter().map(|h| h.join()).collect::<Vec<_>>();
        values.sort_unstable();
        assert_eq!(values.first(), Some(&0));
        assert_eq!(values.last(), Some(&(63 * 63)));
    }
}
