/// Fiber-based handler runtime for `@deferred` / `with k` continuations.
use std::cell::{Cell, RefCell};
use std::ptr;

// ── Struct layouts (repr(C), offsets known to assembly) ──────────────────────

/// Fiber's saved state.  `repr(C)` so assembly can compute offsets.
///
/// Field order must match the constants at the bottom of this file and the
/// assembly stubs exactly.
///
/// Layout:
/// ```text
///   +0   saved_sp:   usize     (fiber stack pointer at suspend)
///   +8   saved_regs: [u64;12]  (callee-saved regs at suspend)
///   +104 stack_ptr:  *mut u8   (raw pointer into stack buffer)
///   +112 stack_len:  usize     (length of stack buffer in bytes)
///   +120 _stack:     Vec<u8>   (owns the allocation; opaque to assembly)
/// ```
#[repr(C)]
pub struct StackSegment {
    pub saved_sp: usize,
    pub saved_regs: [u64; 12],
    /// Raw pointer to the stack buffer (set at allocation, never changes).
    pub stack_ptr: *mut u8,
    /// Length of the stack buffer (set at allocation, never changes).
    pub stack_len: usize,
    /// Heap allocation; `_` prefix = opaque, not touched by assembly.
    _stack: Vec<u8>,
}

/// Handler's save area — stack-allocated in the handler's frame.
///
/// Layout:
/// ```text
///   +0   handler_sp:   usize     (handler stack pointer)
///   +8   handler_regs: [u64;12]  (handler callee-saved regs)
///   +104 segment:      *mut StackSegment
/// ```
#[repr(C)]
pub struct Prompt {
    pub handler_sp: usize,
    pub handler_regs: [u64; 12],
    pub segment: *mut StackSegment,
}

// Prompt is single-threaded; fibers never migrate across threads.
unsafe impl Send for Prompt {}

// ── Thread-locals ─────────────────────────────────────────────────────────────

thread_local! {
    static ACTIVE_PROMPT: Cell<*mut Prompt> = const { Cell::new(ptr::null_mut()) };
    static SEGMENT_POOL: RefCell<Vec<StackSegment>> = const { RefCell::new(Vec::new()) };
    /// Set to `true` by the trampoline epilogue when the fiber exits normally.
    /// `kea_fiber_resume` callers should check this after the call returns.
    static FIBER_IS_DONE: Cell<bool> = const { Cell::new(false) };
}

// ── TLS helpers (called from assembly) ───────────────────────────────────────

/// # Safety
/// May only be called from the fiber assembly stubs on the owning thread.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn kea_active_prompt_get() -> *mut Prompt {
    ACTIVE_PROMPT.with(|c| c.get())
}

/// # Safety
/// May only be called from the fiber assembly stubs on the owning thread.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn kea_active_prompt_set(ptr: *mut Prompt) {
    ACTIVE_PROMPT.with(|c| c.set(ptr));
}

/// Called by the trampoline BEFORE the fiber starts.  Clears the done flag.
/// # Safety
/// Must only be called from the trampoline assembly stub.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn kea_fiber_clear_done() {
    FIBER_IS_DONE.with(|c| c.set(false));
}

/// Called by the trampoline epilogue AFTER the fiber's fn_ptr returns normally.
/// # Safety
/// Must only be called from the trampoline assembly stub.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn kea_fiber_mark_done() {
    FIBER_IS_DONE.with(|c| c.set(true));
}

/// Returns `true` if the most recent `kea_fiber_trampoline` or `kea_fiber_resume`
/// call returned because the fiber completed normally (rather than suspending).
///
/// Call this immediately after `kea_fiber_trampoline` / `kea_fiber_resume` returns.
pub fn fiber_is_done() -> bool {
    FIBER_IS_DONE.with(|c| c.get())
}

/// C-callable version of `fiber_is_done()` for use from MIR-generated code.
///
/// Returns 1 if the most recent fiber call completed normally, 0 if it suspended.
/// # Safety
/// Must be called from the handler context (handler stack, not fiber stack).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn kea_fiber_is_done() -> i64 {
    if FIBER_IS_DONE.with(|c| c.get()) { 1 } else { 0 }
}

/// Heap-allocate a `Prompt` paired with `segment`.
///
/// Returns a raw pointer valid until `kea_free_prompt` is called.
/// Using a heap Prompt avoids the "must not move" constraint, at the cost of
/// one extra allocation per fiber invocation.
///
/// # Safety
/// The caller must call `kea_free_prompt` exactly once when done.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn kea_alloc_prompt(segment: *mut StackSegment) -> *mut Prompt {
    let mut p = Box::new(Prompt {
        handler_sp: 0,
        handler_regs: [0u64; 12],
        segment,
    });
    let ptr = p.as_mut() as *mut Prompt;
    std::mem::forget(p); // caller owns it
    ptr
}

/// Free a heap-allocated `Prompt`.
/// # Safety
/// `prompt` must have been produced by `kea_alloc_prompt`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn kea_free_prompt(prompt: *mut Prompt) {
    if !prompt.is_null() {
        drop(unsafe { Box::from_raw(prompt) });
    }
}

// ── Public API ────────────────────────────────────────────────────────────────

/// Default fiber stack size (64 KiB).
pub const DEFAULT_STACK_SIZE: usize = 64 * 1024;

/// Allocate (or recycle) a `StackSegment`.
///
/// # Safety
/// Caller must call `kea_free_segment` exactly once when done.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn kea_alloc_segment(stack_size: usize) -> *mut StackSegment {
    let seg = SEGMENT_POOL.with(|pool| {
        let mut pool = pool.borrow_mut();
        if let Some(pos) = pool.iter().position(|s| s.stack_len >= stack_size) {
            let mut seg = pool.remove(pos);
            seg.saved_sp = 0;
            seg.saved_regs = [0u64; 12];
            return seg;
        }
        let mut buf = vec![0u8; stack_size];
        let stack_ptr = buf.as_mut_ptr();
        let stack_len = buf.len();
        StackSegment {
            saved_sp: 0,
            saved_regs: [0u64; 12],
            stack_ptr,
            stack_len,
            _stack: buf,
        }
    });
    // Box the segment so it has a stable address we can hand out as a raw pointer.
    // Moving the StackSegment into a Box is safe: `_stack: Vec<u8>` owns heap data
    // that doesn't move when the struct moves; `stack_ptr` points into that heap data.
    Box::into_raw(Box::new(seg))
}

/// Return `seg` to the per-thread pool.
///
/// # Safety
/// `seg` must have been produced by `kea_alloc_segment` and must no longer
/// be referenced by any live continuation.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn kea_free_segment(seg: *mut StackSegment) {
    if seg.is_null() {
        return;
    }
    // Reclaim ownership; unbox to a plain value for compact pool storage.
    let seg_owned = unsafe { *Box::from_raw(seg) };
    SEGMENT_POOL.with(|pool| {
        let mut pool = pool.borrow_mut();
        if pool.len() < 8 {
            pool.push(seg_owned);
        }
        // Otherwise drops here; Box destructor frees the Vec buffer.
    });
}

/// Initialise a stack-allocated `Prompt`.
///
/// # Safety
/// `prompt` and `segment` must be valid non-null pointers.  `prompt` must
/// not be moved after being passed to `kea_fiber_trampoline`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn kea_prompt_init(prompt: *mut Prompt, segment: *mut StackSegment) {
    let p = unsafe { &mut *prompt };
    p.handler_sp = 0;
    p.handler_regs = [0u64; 12];
    p.segment = segment;
}

// ── Assembly-implemented entry points ─────────────────────────────────────────

#[allow(improper_ctypes)]
unsafe extern "C" {
    /// Run `fn_ptr(arg)` on the fiber stack.
    ///
    /// Returns the first suspend value (from `kea_fiber_suspend`), or the
    /// fiber's return value if it never suspends.  Check `fiber_is_done()`
    /// after this call to distinguish normal exit from suspension.
    pub fn kea_fiber_trampoline(prompt: *mut Prompt, fn_ptr: usize, arg: i64) -> i64;

    /// Suspend the current fiber, returning `value` to the handler.
    ///
    /// Returns the resume value provided by `kea_fiber_resume`.
    pub fn kea_fiber_suspend(value: i64) -> i64;

    /// Resume a suspended fiber with `value`.
    ///
    /// Returns the next suspend value, or the fiber's return value if the fiber
    /// completes.  Check `fiber_is_done()` after this call to tell them apart.
    pub fn kea_fiber_resume(prompt: *mut Prompt, value: i64) -> i64;
}

// ── Offset constants (for assembly verification) ──────────────────────────────

pub const SEG_SAVED_SP: usize = 0;
pub const SEG_SAVED_REGS: usize = 8;
pub const SEG_STACK_PTR: usize = 8 + 12 * 8; // 104
pub const SEG_STACK_LEN: usize = 8 + 12 * 8 + 8; // 112

pub const PROMPT_HANDLER_SP: usize = 0;
pub const PROMPT_HANDLER_REGS: usize = 8;
pub const PROMPT_SEGMENT: usize = 8 + 12 * 8; // 104

// ── Tests ─────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use std::mem::offset_of;

    #[test]
    fn segment_field_offsets() {
        assert_eq!(offset_of!(StackSegment, saved_sp), SEG_SAVED_SP);
        assert_eq!(offset_of!(StackSegment, saved_regs), SEG_SAVED_REGS);
        assert_eq!(offset_of!(StackSegment, stack_ptr), SEG_STACK_PTR);
        assert_eq!(offset_of!(StackSegment, stack_len), SEG_STACK_LEN);
    }

    #[test]
    fn prompt_field_offsets() {
        assert_eq!(offset_of!(Prompt, handler_sp), PROMPT_HANDLER_SP);
        assert_eq!(offset_of!(Prompt, handler_regs), PROMPT_HANDLER_REGS);
        assert_eq!(offset_of!(Prompt, segment), PROMPT_SEGMENT);
    }

    #[test]
    fn alloc_free_roundtrip() {
        unsafe {
            let seg = kea_alloc_segment(DEFAULT_STACK_SIZE);
            assert!(!seg.is_null());
            assert!((*seg).stack_len >= DEFAULT_STACK_SIZE);
            assert!(!(*seg).stack_ptr.is_null());
            kea_free_segment(seg);
            // Second alloc recycles.
            let seg2 = kea_alloc_segment(DEFAULT_STACK_SIZE);
            assert!(!seg2.is_null());
            kea_free_segment(seg2);
        }
    }

    #[test]
    fn prompt_init_clears() {
        unsafe {
            let seg = kea_alloc_segment(DEFAULT_STACK_SIZE);
            let mut p = Prompt {
                handler_sp: 0xdead,
                handler_regs: [0xbad; 12],
                segment: ptr::null_mut(),
            };
            kea_prompt_init(&mut p, seg);
            assert_eq!(p.handler_sp, 0);
            assert_eq!(p.handler_regs, [0u64; 12]);
            assert_eq!(p.segment, seg);
            kea_free_segment(seg);
        }
    }

    // ── Fiber round-trip tests ────────────────────────────────────────────────

    /// Fiber that returns immediately without suspending.
    unsafe extern "C" fn fiber_immediate_return(_arg: i64) -> i64 {
        42
    }

    #[test]
    fn fiber_no_suspend_returns_value() {
        unsafe {
            let seg = kea_alloc_segment(DEFAULT_STACK_SIZE);
            let prompt = kea_alloc_prompt(seg);
            let result =
                kea_fiber_trampoline(prompt, fiber_immediate_return as *const () as usize, 0);
            assert_eq!(result, 42);
            kea_free_prompt(prompt);
            kea_free_segment(seg);
        }
    }

    /// Fiber that suspends once then the handler resumes it.
    unsafe extern "C" fn fiber_suspend_once(_arg: i64) -> i64 {
        // Suspend with value 7; expect to receive 99 back.
        let resume_val = unsafe { kea_fiber_suspend(7) };
        assert_eq!(resume_val, 99);
        1000 // final return value
    }

    #[test]
    fn fiber_single_suspend_resume() {
        unsafe {
            let seg = kea_alloc_segment(DEFAULT_STACK_SIZE);
            let prompt = kea_alloc_prompt(seg);

            // First call: fiber suspends, trampoline returns 7.
            let suspend_val =
                kea_fiber_trampoline(prompt, fiber_suspend_once as *const () as usize, 0);
            assert_eq!(suspend_val, 7);
            assert!(!fiber_is_done());

            // Resume with 99; fiber finishes and returns 1000.
            let final_val = kea_fiber_resume(prompt, 99);
            assert_eq!(final_val, 1000);
            assert!(fiber_is_done());

            kea_free_prompt(prompt);
            kea_free_segment(seg);
        }
    }

    /// Fiber that suspends twice.
    unsafe extern "C" fn fiber_suspend_twice(_arg: i64) -> i64 {
        let r1 = unsafe { kea_fiber_suspend(10) };
        let r2 = unsafe { kea_fiber_suspend(30) };
        // Return r1 + r2 as final value so we can observe it
        r1 + r2
    }

    #[test]
    fn fiber_two_suspends() {
        unsafe {
            let seg = kea_alloc_segment(DEFAULT_STACK_SIZE);
            let prompt = kea_alloc_prompt(seg);

            // First suspend: value = 10
            let v1 = kea_fiber_trampoline(prompt, fiber_suspend_twice as *const () as usize, 0);
            assert_eq!(v1, 10);
            assert!(!fiber_is_done());

            // Resume with 20; fiber suspends again with 30
            let v2 = kea_fiber_resume(prompt, 20);
            assert_eq!(v2, 30);
            assert!(!fiber_is_done());

            // Resume with 40; fiber completes, returns 20 + 40 = 60
            let final_val = kea_fiber_resume(prompt, 40);
            assert_eq!(final_val, 60);
            assert!(fiber_is_done());

            kea_free_prompt(prompt);
            kea_free_segment(seg);
        }
    }

    #[test]
    fn fiber_no_suspend_done_flag() {
        unsafe {
            let seg = kea_alloc_segment(DEFAULT_STACK_SIZE);
            let prompt = kea_alloc_prompt(seg);
            let result =
                kea_fiber_trampoline(prompt, fiber_immediate_return as *const () as usize, 0);
            assert_eq!(result, 42);
            assert!(fiber_is_done());
            kea_free_prompt(prompt);
            kea_free_segment(seg);
        }
    }
}
