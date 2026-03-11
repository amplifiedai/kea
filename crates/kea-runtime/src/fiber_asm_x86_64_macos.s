// Kea fiber runtime — x86-64 (Linux; no leading underscore on symbols)
//
// System V AMD64 ABI:
//   Args:         rdi, rsi, rdx, rcx, r8, r9
//   Return:       rax
//   Callee-saved: rbx, rbp, r12-r15
//   Caller-saved: rax, rcx, rdx, rsi, rdi, r8-r11
//
// saved_regs [u64;12]: rbx(+0), rbp(+8), r12(+16), r13(+24), r14(+32), r15(+40),
//                      [+48..+88] = padding
//
// Prompt:
//   +0   handler_sp:   u64
//   +8   handler_regs: [u64;12]  (rbx,rbp,r12-r15 at offsets 8,16,24,32,40,48)
//   +104 segment:      *mut StackSegment
//
// StackSegment:
//   +0   saved_sp:   u64
//   +8   saved_regs: [u64;12]  same layout
//   +104 stack_ptr:  *mut u8
//   +112 stack_len:  u64
//
// External Rust (no_mangle, no underscore on Linux):
//   _kea_active_prompt_get() -> *mut Prompt
//   _kea_active_prompt_set(*mut Prompt) -> ()

.text
.align 4

// ─── kea_fiber_trampoline(prompt: rdi, fn_ptr: rsi, arg: rdx) -> i64 ─────────
//
// Allocates a 16-byte local slot (sub $16, rsp) for a temporary return-value
// store, then saves handler context.  The Prompt.handler_sp points to this
// adjusted rsp so that the epilogue can find the slot.

.globl _kea_fiber_trampoline
_kea_fiber_trampoline:
    sub  $16, %rsp                // 16-byte local slot; rsp now 16-aligned

    // Save handler callee-saved regs to Prompt.handler_regs (+8)
    mov  %rbx,  8(%rdi)
    mov  %rbp, 16(%rdi)
    mov  %r12, 24(%rdi)
    mov  %r13, 32(%rdi)
    mov  %r14, 40(%rdi)
    mov  %r15, 48(%rdi)
    // Save handler rsp (includes our 16-byte slot) to Prompt.handler_sp (+0)
    mov  %rsp, (%rdi)

    mov  %rdi, %r12               // r12 = prompt
    mov  %rsi, %r13               // r13 = fn_ptr
    mov  %rdx, %r14               // r14 = arg

    // Set ACTIVE_PROMPT = prompt (rdi already = prompt)
    call _kea_active_prompt_set    // r12-r15 intact (callee-saved)

    // Compute fiber stack top from Segment
    mov  104(%r12), %rax          // rax = segment
    mov  104(%rax), %r15          // r15 = stack_ptr
    add  112(%rax), %r15          // r15 = stack_ptr + stack_len
    and  $-16, %r15               // align down to 16

    // Clear done flag, then switch to fiber stack and call fn_ptr(arg)
    call _kea_fiber_clear_done     // clears FIBER_IS_DONE; r12-r15 intact
    mov  %r15, %rsp
    mov  %r14, %rdi               // arg
    call *%r13                    // fn_ptr(arg)
    // rax = fiber return value; r12 = prompt (callee-saved, restored by fn_ptr)

    // ── Normal fiber exit ──
    mov  %rax, %r14               // stash return value in r14 (callee-saved)

    // Mark fiber as done
    call _kea_fiber_mark_done      // sets FIBER_IS_DONE=true; r12, r14 intact

    // Clear ACTIVE_PROMPT (still on fiber stack)
    xor  %rdi, %rdi
    call _kea_active_prompt_set    // r12, r14 intact

    // Restore handler rsp (includes our 16-byte local slot)
    mov  (%r12), %rsp

    // Store return value in our local slot at [rsp]
    mov  %r14, (%rsp)

    // Restore handler callee-saved regs using r11 as temp base
    mov  %r12, %r11
    mov   8(%r11), %rbx
    mov  16(%r11), %rbp
    mov  24(%r11), %r12
    mov  32(%r11), %r13
    mov  40(%r11), %r14           // handler's r14 restored, our save is in [rsp]
    mov  48(%r11), %r15

    // Pop return value → rax, then free local slot → rsp = entry_rsp → return addr
    mov  (%rsp), %rax
    add  $16, %rsp                // rsp = entry_rsp (points to return address)
    ret

// ─── kea_fiber_suspend(value: rdi) -> i64 ────────────────────────────────────
//
// At entry: [rsp] = fiber return address (standard call frame).
// Saves fiber state to Segment, restores handler state from Prompt, returns
// `value` as rax.  On resume (kea_fiber_resume called), execution continues
// at the instruction after this function's call site in the fiber.

.globl _kea_fiber_suspend
_kea_fiber_suspend:
    // Allocate 16-byte frame to save suspend value across the call below
    sub  $16, %rsp                // [rsp+16] = fiber ret addr; [rsp] = slot for suspend val
    mov  %rdi, (%rsp)             // [rsp] = suspend value

    call _kea_active_prompt_get    // rax = prompt; [rsp] intact (callee restores rsp)

    mov  %rax, %r10               // r10 = prompt (scratch; survives mov's)
    mov  104(%r10), %r11          // r11 = segment (scratch)

    // Retrieve suspend value; restore rsp to entry state ([rsp] = fiber ret addr)
    mov  (%rsp), %rdi             // rdi = suspend value
    add  $16, %rsp                // rsp = entry rsp; [rsp] = fiber ret addr

    // Save fiber callee-saved regs to Segment.saved_regs (+8)
    mov  %rbx,  8(%r11)
    mov  %rbp, 16(%r11)
    mov  %r12, 24(%r11)
    mov  %r13, 32(%r11)
    mov  %r14, 40(%r11)
    mov  %r15, 48(%r11)

    // Save fiber rsp to Segment.saved_sp (+0).
    // rsp points to the fiber return address.  On resume we restore this rsp
    // and `ret` will pop the fiber return address. ✓
    mov  %rsp, (%r11)

    // Restore handler context from Prompt
    mov   (%r10), %rsp            // handler rsp
    mov   8(%r10), %rbx
    mov  16(%r10), %rbp
    mov  24(%r10), %r12
    mov  32(%r10), %r13
    mov  40(%r10), %r14
    mov  48(%r10), %r15

    // Return suspend value to handler
    mov  %rdi, %rax
    ret

// ─── kea_fiber_resume(prompt: rdi, value: rsi) ───────────────────────────────
//
// Saves handler context to Prompt, sets ACTIVE_PROMPT, restores fiber context
// from Segment, then rets into the fiber with rax = value.

.globl _kea_fiber_resume
_kea_fiber_resume:
    // Save handler callee-saved regs + rsp to Prompt
    mov  %rbx,  8(%rdi)
    mov  %rbp, 16(%rdi)
    mov  %r12, 24(%rdi)
    mov  %r13, 32(%rdi)
    mov  %r14, 40(%rdi)
    mov  %r15, 48(%rdi)
    mov  %rsp, (%rdi)

    mov  %rdi, %r12               // r12 = prompt (callee-saved, survives call)
    mov  %rsi, %r13               // r13 = resume value (callee-saved, survives call)

    // Set ACTIVE_PROMPT = prompt (rdi already = prompt)
    call _kea_active_prompt_set    // r12, r13 intact

    // Load segment
    mov  104(%r12), %r11          // r11 = segment (scratch; not clobbered by mov's)

    // Load fiber rsp into r10 (scratch; not clobbered by mov's)
    mov  (%r11), %r10             // r10 = fiber saved_sp

    // Temporarily stash resume value in Segment.saved_sp so it survives
    // the register restore sequence (which overwrites r12, r13).
    mov  %r13, (%r11)

    // Restore fiber callee-saved regs
    mov   8(%r11), %rbx
    mov  16(%r11), %rbp
    mov  24(%r11), %r12
    mov  32(%r11), %r13
    mov  40(%r11), %r14
    mov  48(%r11), %r15

    // Switch to fiber stack
    mov  %r10, %rsp

    // Load resume value from temp slot → rax (fiber sees it as suspend return)
    mov  (%r11), %rax

    ret                           // → fiber return address; rax = resume value
