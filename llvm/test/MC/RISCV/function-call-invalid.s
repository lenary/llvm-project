# RUN: not llvm-mc -triple riscv32 < %s 2>&1 | FileCheck %s

call 1234 # CHECK: :[[@LINE]]:6: error: register must be GPR (x0-x31)
call %pcrel_hi(1234) # CHECK: :[[@LINE]]:6: error: register must be GPR (x0-x31)
call %pcrel_lo(1234) # CHECK: :[[@LINE]]:6: error: register must be GPR (x0-x31)
call %pcrel_hi(foo) # CHECK: :[[@LINE]]:6: error: register must be GPR (x0-x31)
call %pcrel_lo(foo) # CHECK: :[[@LINE]]:6: error: register must be GPR (x0-x31)
call %hi(1234) # CHECK: :[[@LINE]]:6: error: register must be GPR (x0-x31)
call %lo(1234) # CHECK: :[[@LINE]]:6: error: register must be GPR (x0-x31)
call %hi(foo) # CHECK: :[[@LINE]]:6: error: register must be GPR (x0-x31)
call %lo(foo) # CHECK: :[[@LINE]]:6: error: register must be GPR (x0-x31)
call foo, bar # CHECK: :[[@LINE]]:6: error: register must be GPR (x0-x31)
