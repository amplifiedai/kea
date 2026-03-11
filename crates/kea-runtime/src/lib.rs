use crossbeam_deque::{Injector, Steal, Stealer, Worker};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{mpsc, Arc, Condvar, Mutex, OnceLock};
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

#[derive(Default)]
struct RuntimeCounters {
    enqueued: AtomicU64,
    executed: AtomicU64,
    local_pops: AtomicU64,
    injector_steals: AtomicU64,
    peer_steals: AtomicU64,
    park_waits: AtomicU64,
    wake_signals: AtomicU64,
}

/// Runtime counter snapshot for observability and tuning.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct RuntimeStats {
    pub enqueued: u64,
    pub executed: u64,
    pub local_pops: u64,
    pub injector_steals: u64,
    pub peer_steals: u64,
    pub park_waits: u64,
    pub wake_signals: u64,
}

impl RuntimeCounters {
    fn snapshot(&self) -> RuntimeStats {
        RuntimeStats {
            enqueued: self.enqueued.load(Ordering::Relaxed),
            executed: self.executed.load(Ordering::Relaxed),
            local_pops: self.local_pops.load(Ordering::Relaxed),
            injector_steals: self.injector_steals.load(Ordering::Relaxed),
            peer_steals: self.peer_steals.load(Ordering::Relaxed),
            park_waits: self.park_waits.load(Ordering::Relaxed),
            wake_signals: self.wake_signals.load(Ordering::Relaxed),
        }
    }

    fn reset(&self) {
        self.enqueued.store(0, Ordering::Relaxed);
        self.executed.store(0, Ordering::Relaxed);
        self.local_pops.store(0, Ordering::Relaxed);
        self.injector_steals.store(0, Ordering::Relaxed);
        self.peer_steals.store(0, Ordering::Relaxed);
        self.park_waits.store(0, Ordering::Relaxed);
        self.wake_signals.store(0, Ordering::Relaxed);
    }
}

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
    counters: RuntimeCounters,
}

impl RuntimeInner {
    fn enqueue(&self, job: JobEnvelope) {
        self.injector.push(job);
        self.counters.enqueued.fetch_add(1, Ordering::Relaxed);
        self.counters.wake_signals.fetch_add(1, Ordering::Relaxed);
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
            counters: RuntimeCounters::default(),
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

    /// Snapshot internal runtime counters.
    pub fn stats(&self) -> RuntimeStats {
        self.inner.counters.snapshot()
    }

    /// Reset runtime counters back to zero.
    pub fn reset_stats(&self) {
        self.inner.counters.reset();
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

enum WorkSource {
    Local,
    InjectorSteal,
    PeerSteal,
}

fn try_pop_work(
    local: &Worker<JobEnvelope>,
    inner: &RuntimeInner,
    worker_id: usize,
) -> Option<(JobEnvelope, WorkSource)> {
    if let Some(local_job) = local.pop() {
        return Some((local_job, WorkSource::Local));
    }

    match inner.injector.steal_batch_and_pop(local) {
        Steal::Success(job) => return Some((job, WorkSource::InjectorSteal)),
        Steal::Retry | Steal::Empty => {}
    }

    for (idx, stealer) in inner.stealers.iter().enumerate() {
        if idx == worker_id {
            continue;
        }
        match stealer.steal_batch_and_pop(local) {
            Steal::Success(job) => return Some((job, WorkSource::PeerSteal)),
            Steal::Retry | Steal::Empty => {}
        }
    }

    None
}

fn worker_loop(worker_id: usize, local: Worker<JobEnvelope>, inner: Arc<RuntimeInner>) {
    loop {
        if let Some((job, source)) = try_pop_work(&local, &inner, worker_id) {
            match source {
                WorkSource::Local => {
                    inner.counters.local_pops.fetch_add(1, Ordering::Relaxed);
                }
                WorkSource::InjectorSteal => {
                    inner
                        .counters
                        .injector_steals
                        .fetch_add(1, Ordering::Relaxed);
                }
                WorkSource::PeerSteal => {
                    inner.counters.peer_steals.fetch_add(1, Ordering::Relaxed);
                }
            }
            job.run();
            inner.counters.executed.fetch_add(1, Ordering::Relaxed);
            continue;
        }

        if inner.shutdown.load(Ordering::Acquire) && inner.injector.is_empty() && local.is_empty() {
            break;
        }

        let guard = inner.park.mutex.lock().expect("park mutex poisoned");
        inner.counters.park_waits.fetch_add(1, Ordering::Relaxed);
        let _ = inner
            .park
            .cv
            .wait_timeout(guard, Duration::from_millis(2))
            .expect("park condvar poisoned");
    }
}

// ---------------------------------------------------------------------------
// Global runtime singleton
// ---------------------------------------------------------------------------

/// Lazily-initialised global work-stealing runtime.
///
/// Thread count defaults to available parallelism (core count). Override
/// via the `KEA_THREADS` environment variable.
pub fn global_runtime() -> &'static Runtime {
    static RT: OnceLock<Runtime> = OnceLock::new();
    RT.get_or_init(|| {
        let threads = std::env::var("KEA_THREADS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or_else(|| {
                std::thread::available_parallelism()
                    .map(|n| n.get())
                    .unwrap_or(4)
            });
        Runtime::new(threads)
    })
}

// ---------------------------------------------------------------------------
// C-ABI bridge for Par lowering
// ---------------------------------------------------------------------------
//
// Kea closure heap block layout (pointer-sized fields):
//   offset 0: fn_ptr  — the actual function pointer
//   offset 8: cap_0   — first captured value
//   offset 16: cap_1  — second captured value
//   ...
//
// Calling convention for a `fn(A) -> B` closure:
//   fn_ptr(env_ptr: *mut u8, arg: usize) -> usize
// where `env_ptr` is the closure block pointer itself.
//
// Calling convention for a `fn() -> A` thunk closure:
//   fn_ptr(env_ptr: *mut u8) -> usize

/// Type-erased parallel map.
///
/// `items_ptr` points to an array of `count` pointer-sized values.
/// `closure_ptr` points to a Kea closure block (fn_ptr at offset 0).
/// `output_ptr` points to a pre-allocated array of `count` pointer-sized slots.
///
/// v1: sequential execution — result semantics identical to parallel, without
/// the overhead. Swap the body to `parallel_map` once the closure-passing
/// mechanism is verified end-to-end.
///
/// # Safety
/// All pointers must be valid for the duration of the call. `count` must
/// accurately reflect the length of both arrays.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __kea_par_map_raw(
    items_ptr: *mut usize,
    count: i64,
    closure_ptr: *mut u8,
    output_ptr: *mut usize,
) {
    // SAFETY: caller guarantees all pointers are valid and count is correct.
    unsafe {
        // Load fn_ptr from offset 0 of the closure block.
        let fn_ptr: unsafe extern "C" fn(*mut u8, usize) -> usize =
            std::mem::transmute(*(closure_ptr as *const usize));
        for i in 0..count as usize {
            let item = *items_ptr.add(i);
            *output_ptr.add(i) = fn_ptr(closure_ptr, item);
        }
    }
}

/// Evaluate two independent thunks sequentially, returning both results
/// packed into a pair (a_result, b_result) via output pointers.
///
/// `a_ptr` and `b_ptr` are Kea closure blocks for `fn() -> A` and `fn() -> B`.
/// `out_a` and `out_b` are caller-allocated slots for the results.
///
/// # Safety
/// All pointers must be valid for the duration of the call.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __kea_par_all2_raw(
    a_ptr: *mut u8,
    b_ptr: *mut u8,
    out_a: *mut usize,
    out_b: *mut usize,
) {
    // SAFETY: caller guarantees all pointers are valid.
    unsafe {
        let fn_a: unsafe extern "C" fn(*mut u8) -> usize =
            std::mem::transmute(*(a_ptr as *const usize));
        let fn_b: unsafe extern "C" fn(*mut u8) -> usize =
            std::mem::transmute(*(b_ptr as *const usize));
        *out_a = fn_a(a_ptr);
        *out_b = fn_b(b_ptr);
    }
}

/// Evaluate three independent thunks sequentially.
///
/// # Safety
/// All pointers must be valid for the duration of the call.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn __kea_par_all3_raw(
    a_ptr: *mut u8,
    b_ptr: *mut u8,
    c_ptr: *mut u8,
    out_a: *mut usize,
    out_b: *mut usize,
    out_c: *mut usize,
) {
    // SAFETY: caller guarantees all pointers are valid.
    unsafe {
        let fn_a: unsafe extern "C" fn(*mut u8) -> usize =
            std::mem::transmute(*(a_ptr as *const usize));
        let fn_b: unsafe extern "C" fn(*mut u8) -> usize =
            std::mem::transmute(*(b_ptr as *const usize));
        let fn_c: unsafe extern "C" fn(*mut u8) -> usize =
            std::mem::transmute(*(c_ptr as *const usize));
        *out_a = fn_a(a_ptr);
        *out_b = fn_b(b_ptr);
        *out_c = fn_c(c_ptr);
    }
}

#[cfg(test)]
mod tests {
    use super::{EffectHint, Runtime, RuntimeStats};
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
        let stats = runtime.stats();
        assert_eq!(stats.enqueued, 1000);
        assert_eq!(stats.executed, 1000);
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

    #[test]
    fn stats_reset_clears_counters() {
        let runtime = Runtime::new(2);
        let handles = (0..32)
            .map(|_| runtime.spawn(|| 1usize))
            .collect::<Vec<_>>();
        for handle in handles {
            assert_eq!(handle.join(), 1);
        }

        let before_reset = runtime.stats();
        assert!(before_reset.enqueued >= 32);
        assert!(before_reset.executed >= 32);

        runtime.reset_stats();
        let after_reset = runtime.stats();
        assert_eq!(after_reset, RuntimeStats::default());
    }
}
