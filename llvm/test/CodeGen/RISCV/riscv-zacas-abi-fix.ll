; RUN: opt %s -S -riscv-zacas-abi-fix -mtriple=riscv64 -mattr=+a,+zacas | FileCheck %s --check-prefixes=CHECK,ZACAS
; RUN: opt %s -S -passes=riscv-zacas-abi-fix -mtriple=riscv64 -mattr=+a,+zacas | FileCheck %s --check-prefixes=CHECK,ZACAS
; RUN: opt %s -S -riscv-zacas-abi-fix -mtriple=riscv64 -mattr=+a | FileCheck %s --check-prefixes=CHECK,NOZACAS
; RUN: opt %s -S -passes=riscv-zacas-abi-fix -mtriple=riscv64 -mattr=+a | FileCheck %s --check-prefixes=CHECK,NOZACAS

; A cmpxchg with a seq_cst failure ordering needs a leading fence for the
; broadest atomics ABI compatibility, but only when Zacas is enabled.
define i32 @cmpxchg_seq_cst_failure(ptr %ptr, i32 %cmp, i32 %new) {
; CHECK-LABEL: @cmpxchg_seq_cst_failure(
; ZACAS-NEXT:    fence seq_cst
; NOZACAS-NOT:   fence
; CHECK-NEXT:    [[RES:%.*]] = cmpxchg ptr [[PTR:%.*]], i32 [[CMP:%.*]], i32 [[NEW:%.*]] seq_cst seq_cst
; CHECK-NEXT:    [[VAL:%.*]] = extractvalue { i32, i1 } [[RES]], 0
; CHECK-NEXT:    ret i32 [[VAL]]
;
  %res = cmpxchg ptr %ptr, i32 %cmp, i32 %new seq_cst seq_cst
  %val = extractvalue { i32, i1 } %res, 0
  ret i32 %val
}

; A cmpxchg with a weaker failure ordering never needs a leading fence.
define i32 @cmpxchg_monotonic_failure(ptr %ptr, i32 %cmp, i32 %new) {
; CHECK-LABEL: @cmpxchg_monotonic_failure(
; CHECK-NEXT:    [[RES:%.*]] = cmpxchg ptr [[PTR:%.*]], i32 [[CMP:%.*]], i32 [[NEW:%.*]] seq_cst monotonic
; CHECK-NEXT:    [[VAL:%.*]] = extractvalue { i32, i1 } [[RES]], 0
; CHECK-NEXT:    ret i32 [[VAL]]
;
  %res = cmpxchg ptr %ptr, i32 %cmp, i32 %new seq_cst monotonic
  %val = extractvalue { i32, i1 } %res, 0
  ret i32 %val
}
