// Kea fiber runtime — AArch64 Linux (no leading underscore on symbols)
// This file is identical to fiber_asm_aarch64.s except symbol references
// use kea_active_prompt_get / kea_active_prompt_set without underscore prefix.

.text
.align 4

.globl kea_fiber_trampoline
kea_fiber_trampoline:
    stp  x19, x20, [x0, #8]
    stp  x21, x22, [x0, #24]
    stp  x23, x24, [x0, #40]
    stp  x25, x26, [x0, #56]
    stp  x27, x28, [x0, #72]
    stp  x29, x30, [x0, #88]
    mov  x10, sp
    str  x10, [x0, #0]

    mov  x19, x0
    mov  x20, x1
    mov  x21, x2

    bl   kea_active_prompt_set

    ldr  x9,  [x19, #104]
    ldr  x22, [x9,  #104]
    ldr  x10, [x9,  #112]
    add  x22, x22, x10
    and  x22, x22, #~15

    bl   kea_fiber_clear_done
    mov  sp,  x22
    mov  x0,  x21
    blr  x20

    mov  x21, x0
    bl   kea_fiber_mark_done
    mov  x0,  #0
    bl   kea_active_prompt_set

    ldr  x10, [x19, #0]
    mov  sp,  x10

    str  x21, [sp, #-16]!

    mov  x9,  x19
    ldp  x19, x20, [x9, #8]
    ldp  x21, x22, [x9, #24]
    ldp  x23, x24, [x9, #40]
    ldp  x25, x26, [x9, #56]
    ldp  x27, x28, [x9, #72]
    ldp  x29, x30, [x9, #88]

    ldr  x0,  [sp], #16
    ret

.globl kea_fiber_suspend
kea_fiber_suspend:
    stp  x30, x0, [sp, #-16]!
    bl   kea_active_prompt_get
    mov  x9,  x0
    ldr  x10, [x9, #104]
    ldp  x30, x11, [sp], #16

    stp  x19, x20, [x10, #8]
    stp  x21, x22, [x10, #24]
    stp  x23, x24, [x10, #40]
    stp  x25, x26, [x10, #56]
    stp  x27, x28, [x10, #72]
    stp  x29, x30, [x10, #88]
    mov  x12, sp
    str  x12, [x10, #0]

    ldr  x12, [x9, #0]
    ldp  x19, x20, [x9, #8]
    ldp  x21, x22, [x9, #24]
    ldp  x23, x24, [x9, #40]
    ldp  x25, x26, [x9, #56]
    ldp  x27, x28, [x9, #72]
    ldp  x29, x30, [x9, #88]
    mov  sp,  x12

    mov  x0,  x11
    ret

.globl kea_fiber_resume
kea_fiber_resume:
    stp  x19, x20, [x0, #8]
    stp  x21, x22, [x0, #24]
    stp  x23, x24, [x0, #40]
    stp  x25, x26, [x0, #56]
    stp  x27, x28, [x0, #72]
    stp  x29, x30, [x0, #88]
    mov  x10, sp
    str  x10, [x0, #0]

    mov  x19, x0
    mov  x20, x1
    bl   kea_active_prompt_set

    ldr  x9,  [x19, #104]
    ldr  x10, [x9, #0]
    str  x20, [x9, #0]

    ldp  x19, x20, [x9, #8]
    ldp  x21, x22, [x9, #24]
    ldp  x23, x24, [x9, #40]
    ldp  x25, x26, [x9, #56]
    ldp  x27, x28, [x9, #72]
    ldp  x29, x30, [x9, #88]

    mov  sp,  x10
    ldr  x0,  [x9, #0]
    ret
