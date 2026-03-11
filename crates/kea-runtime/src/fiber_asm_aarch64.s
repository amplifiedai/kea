// Kea fiber runtime — AArch64 (macOS/Apple Silicon and Linux arm64)
//
// AArch64 AAPCS64:
//   Arg regs:      x0-x7   (callers pass, callee may clobber)
//   Return:        x0
//   Callee-saved:  x19-x28, x29 (fp), x30 (lr)
//   Scratch (IP):  x16, x17 (may be used by call veneers, NOT saved by callees)
//   Caller-saved:  x0-x15, x16, x17
//
// bl clobbers x30 and may clobber x0-x15, x16, x17.
// bl does NOT clobber x19-x29 (callee-saved).
//
// Struct offsets (repr(C)):
//
// Prompt:
//   +0   handler_sp:   u64
//   +8   handler_regs: [u64;12]  (x19-x28 = [0..9], x29 = [10], x30 = [11])
//   +104 segment:      *mut StackSegment
//
// StackSegment:
//   +0   saved_sp:   u64
//   +8   saved_regs: [u64;12]  (same register order)
//   +104 stack_ptr:  *mut u8
//   +112 stack_len:  u64
//
// External Rust helpers (no_mangle):
//   kea_active_prompt_get() -> *mut Prompt    [macOS: _kea_active_prompt_get]
//   kea_active_prompt_set(*mut Prompt) -> ()  [macOS: _kea_active_prompt_set]

.text
.align 4

// ─── kea_fiber_trampoline(prompt: x0, fn_ptr: x1, arg: x2) -> i64 ───────────
//
// Saves handler callee-saved regs + sp to Prompt, sets ACTIVE_PROMPT,
// switches to the fiber stack, calls fn_ptr(arg).
//
// On normal fiber exit (fn_ptr returns): restores handler context, returns
// fiber's return value to the trampoline's caller.
//
// On fiber suspend (kea_fiber_suspend called): the suspend function restores
// handler context directly from Prompt and rets to the handler's lr — the
// trampoline's body is bypassed. This is correct: from the handler's perspective
// kea_fiber_trampoline "returns" with the suspend value.
//
// Subsequent kea_fiber_resume calls update Prompt to point back to the resume
// call site, so future suspends return to the right place.

.globl _kea_fiber_trampoline
_kea_fiber_trampoline:
    // ── Save handler callee-saved regs to Prompt.handler_regs (+8) ──
    stp  x19, x20, [x0, #8]
    stp  x21, x22, [x0, #24]
    stp  x23, x24, [x0, #40]
    stp  x25, x26, [x0, #56]
    stp  x27, x28, [x0, #72]
    stp  x29, x30, [x0, #88]      // x30 = handler lr (return addr from trampoline's caller)
    // ── Save handler sp to Prompt.handler_sp (+0) ──
    mov  x10, sp
    str  x10, [x0, #0]

    // ── Stash prompt / fn_ptr / arg in callee-saved regs ──
    mov  x19, x0                   // x19 = prompt  (survives bl, blr)
    mov  x20, x1                   // x20 = fn_ptr  (survives bl)
    mov  x21, x2                   // x21 = arg     (survives bl)

    // ── Set ACTIVE_PROMPT = prompt (x0 already = prompt) ──
    bl   _kea_active_prompt_set    // clobbers x0-x15, x30; x19-x29 intact

    // ── Compute fiber stack top from Segment ──
    ldr  x9,  [x19, #104]         // x9  = segment
    ldr  x22, [x9,  #104]         // x22 = stack_ptr
    ldr  x10, [x9,  #112]         // x10 = stack_len
    add  x22, x22, x10            // x22 = stack top (one-past-end of buffer)
    and  x22, x22, #~15           // align down to 16

    // ── Switch to fiber stack and call fn_ptr(arg) ──
    mov  sp,  x22
    mov  x0,  x21
    blr  x20                      // fiber runs; returns here on NORMAL exit
    // x0 = fiber return value; x19 = prompt (callee-saved, restored by fn_ptr)

    // ── Normal fiber exit path ──
    // Save return value in x21 (callee-saved, survives the bl below).
    mov  x21, x0

    // Clear ACTIVE_PROMPT (still on fiber stack — safe, has plenty of space)
    mov  x0,  #0
    bl   _kea_active_prompt_set    // x19 = prompt still intact after bl

    // Restore handler sp (x19 = prompt, still valid)
    ldr  x10, [x19, #0]
    mov  sp,  x10                  // back on handler stack

    // Push return value onto handler stack before clobbering x21 with ldp
    str  x21, [sp, #-16]!         // sp aligned (handler sp was aligned at save time)

    // Restore handler callee-saved regs. Use x9 as temp base so we don't
    // clobber x19 before we finish reading from it.
    mov  x9,  x19
    ldp  x19, x20, [x9, #8]
    ldp  x21, x22, [x9, #24]
    ldp  x23, x24, [x9, #40]
    ldp  x25, x26, [x9, #56]
    ldp  x27, x28, [x9, #72]
    ldp  x29, x30, [x9, #88]

    // Pop return value → x0, restore sp
    ldr  x0,  [sp], #16
    ret

// ─── kea_fiber_suspend(value: x0) -> i64 ─────────────────────────────────────
//
// Called from fiber code.  Saves fiber state to Segment, restores handler
// state from Prompt, returns `value` as if kea_fiber_trampoline (or a prior
// kea_fiber_resume call) returned it.
//
// When kea_fiber_resume is called later, execution resumes at the instruction
// after the `bl _kea_fiber_suspend` call in the fiber.

.globl _kea_fiber_suspend
_kea_fiber_suspend:
    // Entry: x0 = suspend value, x30 = fiber's return address (lr)
    //        x19-x29 = fiber's callee-saved regs, sp = fiber's stack

    // Push lr and suspend value to fiber stack (16-byte aligned store).
    // This frees x30 for the upcoming bl (which clobbers x30).
    stp  x30, x0, [sp, #-16]!

    // Get ACTIVE_PROMPT → x0.  bl clobbers x0-x15 and x30.
    // x19-x29 (fiber's callee-saved) are NOT clobbered.
    bl   _kea_active_prompt_get   // x0 = prompt
    mov  x9,  x0                  // x9 = prompt (scratch; not clobbered by ldp's)

    // Load segment from Prompt.segment (+104)
    ldr  x10, [x9, #104]          // x10 = segment (scratch)

    // Restore lr and suspend value that we pushed
    ldp  x30, x11, [sp], #16     // x30 = fiber lr, x11 = suspend value

    // Save fiber callee-saved regs to Segment.saved_regs (+8)
    stp  x19, x20, [x10, #8]
    stp  x21, x22, [x10, #24]
    stp  x23, x24, [x10, #40]
    stp  x25, x26, [x10, #56]
    stp  x27, x28, [x10, #72]
    stp  x29, x30, [x10, #88]    // x29=fp, x30=fiber lr

    // Save fiber sp to Segment.saved_sp (+0)
    mov  x12, sp
    str  x12, [x10, #0]

    // Restore handler regs from Prompt.handler_regs (+8)
    ldr  x12, [x9, #0]           // handler_sp
    ldp  x19, x20, [x9, #8]
    ldp  x21, x22, [x9, #24]
    ldp  x23, x24, [x9, #40]
    ldp  x25, x26, [x9, #56]
    ldp  x27, x28, [x9, #72]
    ldp  x29, x30, [x9, #88]    // x30 = handler lr
    mov  sp,  x12                // switch to handler stack

    // Return suspend value to handler
    mov  x0,  x11
    ret                          // → handler lr (trampoline or kea_fiber_resume's caller)

// ─── kea_fiber_resume(prompt: x0, value: x1) ─────────────────────────────────
//
// Saves current (handler) state to Prompt (so next suspend returns here),
// sets ACTIVE_PROMPT, then restores fiber state from Segment and rets
// into the fiber with x0 = value.

.globl _kea_fiber_resume
_kea_fiber_resume:
    // ── Save handler callee-saved regs to Prompt.handler_regs (+8) ──
    stp  x19, x20, [x0, #8]
    stp  x21, x22, [x0, #24]
    stp  x23, x24, [x0, #40]
    stp  x25, x26, [x0, #56]
    stp  x27, x28, [x0, #72]
    stp  x29, x30, [x0, #88]
    mov  x10, sp
    str  x10, [x0, #0]

    // Stash prompt and resume value in callee-saved regs
    mov  x19, x0                  // x19 = prompt (survives bl)
    mov  x20, x1                  // x20 = resume value (survives bl)

    // Set ACTIVE_PROMPT = prompt (x0 already = prompt)
    bl   _kea_active_prompt_set   // x19, x20 intact after bl (callee-saved)

    // Load segment from Prompt.segment (+104)
    ldr  x9,  [x19, #104]        // x9 = segment (scratch; survives ldp's)

    // Load fiber sp into a scratch reg (must happen before we clobber x9's address
    // slot by writing the resume value there).
    ldr  x10, [x9, #0]           // x10 = fiber saved_sp (scratch; survives ldp's)

    // Temporarily stash resume value in Segment.saved_sp so it survives the ldp
    // restore sequence (which overwrites x19-x30).  x9 and x10 are scratch regs
    // not touched by ldp.
    str  x20, [x9, #0]           // Segment.saved_sp ← resume value (temp)

    // Restore fiber callee-saved regs from Segment.saved_regs (+8)
    ldp  x19, x20, [x9, #8]
    ldp  x21, x22, [x9, #24]
    ldp  x23, x24, [x9, #40]
    ldp  x25, x26, [x9, #56]
    ldp  x27, x28, [x9, #72]
    ldp  x29, x30, [x9, #88]    // x30 = fiber lr

    // Switch to fiber stack
    mov  sp,  x10

    // Load resume value from temp slot (x9 = segment, still valid)
    ldr  x0,  [x9, #0]

    ret                          // → fiber lr; fiber sees x0 = resume value
