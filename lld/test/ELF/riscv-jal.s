# REQUIRES: riscv

# RUN: llvm-mc -filetype=obj -triple=riscv32-unknown-elf -mattr=-relax %s -o %t.rv32.o
# RUN: llvm-mc -filetype=obj -triple=riscv64-unknown-elf -mattr=-relax %s -o %t.rv64.o

# RUN: ld.lld %t.rv32.o --defsym foo=_start+4 --defsym bar=_start -o %t.rv32
# RUN: ld.lld %t.rv64.o --defsym foo=_start+4 --defsym bar=_start -o %t.rv64
# RUN: llvm-objdump -d %t.rv32 | FileCheck %s --check-prefix=CHECK-32
# RUN: llvm-objdump -d %t.rv64 | FileCheck %s --check-prefix=CHECK-64
# CHECK-32: 0040006f    j   0x110b8
# CHECK-32: ffdff0ef    jal 0x110b4
# CHECK-64: 0040006f    j   0x11124
# CHECK-64: ffdff0ef    jal 0x11120

# RUN: ld.lld %t.rv32.o --defsym foo=_start+0xffffe --defsym bar=_start+4-0x100000 -o %t.rv32.limits
# RUN: ld.lld %t.rv64.o --defsym foo=_start+0xffffe --defsym bar=_start+4-0x100000 -o %t.rv64.limits
# RUN: llvm-objdump -d %t.rv32.limits | FileCheck --check-prefix=LIMITS-32 %s
# RUN: llvm-objdump -d %t.rv64.limits | FileCheck --check-prefix=LIMITS-64 %s
# LIMITS-32:      7ffff06f j   0x1110b2
# LIMITS-32-NEXT: 800000ef jal 0xfff110b8
# LIMITS-64:      7ffff06f j   0x11111e
# LIMITS-64-NEXT: 800000ef jal 0xfffffffffff11124

# RUN: not ld.lld %t.rv32.o --defsym foo=_start+0x100000 --defsym bar=_start+4-0x100002 -o /dev/null 2>&1 | FileCheck --check-prefix=ERROR-RANGE %s
# RUN: not ld.lld %t.rv64.o --defsym foo=_start+0x100000 --defsym bar=_start+4-0x100002 -o /dev/null 2>&1 | FileCheck --check-prefix=ERROR-RANGE %s
# ERROR-RANGE: relocation R_RISCV_JAL out of range: 1048576 is not in [-1048576, 1048575]; references 'foo'
# ERROR-RANGE: relocation R_RISCV_JAL out of range: -1048578 is not in [-1048576, 1048575]; references 'bar'

# RUN: not ld.lld %t.rv32.o --defsym foo=_start+1 --defsym bar=_start+4+3 -o /dev/null 2>&1 | FileCheck --check-prefix=ERROR-ALIGN %s
# RUN: not ld.lld %t.rv64.o --defsym foo=_start+1 --defsym bar=_start+4+3 -o /dev/null 2>&1 | FileCheck --check-prefix=ERROR-ALIGN %s
# ERROR-ALIGN: improper alignment for relocation R_RISCV_JAL: 0x1 is not aligned to 2 bytes
# ERROR-ALIGN: improper alignment for relocation R_RISCV_JAL: 0x3 is not aligned to 2 bytes

.global _start

_start:
    jal x0, foo
    jal x1, bar
