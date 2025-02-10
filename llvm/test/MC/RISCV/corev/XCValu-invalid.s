# RUN: not llvm-mc -triple=riscv32 --mattr=+xcvalu %s 2>&1 \
# RUN:        | FileCheck %s --check-prefixes=CHECK-ERROR

cv.addrnr t0, t1, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.addrnr t0, 0, t2
# CHECK-ERROR: register must be GPR (x0-x31)

cv.addrnr 0, t1, t2
# CHECK-ERROR: register must be GPR (x0-x31)

cv.addrnr t0, t1
# CHECK-ERROR: too few operands for instruction

cv.addrnr t0, t1, t2, a0
# CHECK-ERROR: invalid operand for instruction

cv.addun t0, t1, t2, -1
# CHECK-ERROR: immediate must be an integer in the range [0, 31]

cv.addun t0, t1, t2, 32
# CHECK-ERROR: immediate must be an integer in the range [0, 31]

cv.addun t0, t1, t2, a0
# CHECK-ERROR: immediate must be an integer in the range [0, 31]

cv.addun t0, t1, 0, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.addun t0, 0, t2, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.addun 0, t1, t2, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.addun t0, t1, t2
# CHECK-ERROR: too few operands for instruction

cv.addun t0, t1, t2, 0, a0
# CHECK-ERROR: invalid operand for instruction

cv.extbz t0, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.extbz 0, t1
# CHECK-ERROR: register must be GPR (x0-x31)

cv.extbz t0
# CHECK-ERROR: too few operands for instruction

cv.extbz t0, t1, t2
# CHECK-ERROR: invalid operand for instruction

cv.addnr t0, t1, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.addnr t0, 0, t2
# CHECK-ERROR: register must be GPR (x0-x31)

cv.addnr 0, t1, t2
# CHECK-ERROR: register must be GPR (x0-x31)

cv.addnr t0, t1
# CHECK-ERROR: too few operands for instruction

cv.addnr t0, t1, t2, a0
# CHECK-ERROR: invalid operand for instruction

cv.clipu t0, t1, -1
# CHECK-ERROR: immediate must be an integer in the range [0, 31]

cv.clipu t0, t1, 32
# CHECK-ERROR: immediate must be an integer in the range [0, 31]

cv.clipu t0, t1, a0
# CHECK-ERROR: immediate must be an integer in the range [0, 31]

cv.clipu t0, 0, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.clipu 0, t1, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.clipu t0, t1
# CHECK-ERROR: too few operands for instruction

cv.clipu t0, t1, 0, 0
# CHECK-ERROR: invalid operand for instruction

cv.minu t0, t1, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.minu t0, 0, t2
# CHECK-ERROR: register must be GPR (x0-x31)

cv.minu 0, t1, t2
# CHECK-ERROR: register must be GPR (x0-x31)

cv.minu t0, t1
# CHECK-ERROR: too few operands for instruction

cv.minu t0, t1, t2, a0
# CHECK-ERROR: invalid operand for instruction

cv.abs t0, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.abs 0, t1
# CHECK-ERROR: register must be GPR (x0-x31)

cv.abs t0
# CHECK-ERROR: too few operands for instruction

cv.abs t0, t1, t2
# CHECK-ERROR: invalid operand for instruction

cv.addrn t0, t1, t2, -1
# CHECK-ERROR: immediate must be an integer in the range [0, 31]

cv.addrn t0, t1, t2, 32
# CHECK-ERROR: immediate must be an integer in the range [0, 31]

cv.addrn t0, t1, t2, a0
# CHECK-ERROR: immediate must be an integer in the range [0, 31]

cv.addrn t0, t1, 0, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.addrn t0, 0, t2, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.addrn 0, t1, t2, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.addrn t0, t1, t2
# CHECK-ERROR: too few operands for instruction

cv.addrn t0, t1, t2, 0, a0
# CHECK-ERROR: invalid operand for instruction

cv.suburn t0, t1, t2, -1
# CHECK-ERROR: immediate must be an integer in the range [0, 31]

cv.suburn t0, t1, t2, 32
# CHECK-ERROR: immediate must be an integer in the range [0, 31]

cv.suburn t0, t1, t2, a0
# CHECK-ERROR: immediate must be an integer in the range [0, 31]

cv.suburn t0, t1, 0, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.suburn t0, 0, t2, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.suburn 0, t1, t2, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.suburn t0, t1, t2
# CHECK-ERROR: too few operands for instruction

cv.suburn t0, t1, t2, 0, a0
# CHECK-ERROR: invalid operand for instruction

cv.clip t0, t1, -1
# CHECK-ERROR: immediate must be an integer in the range [0, 31]

cv.clip t0, t1, 32
# CHECK-ERROR: immediate must be an integer in the range [0, 31]

cv.clip t0, t1, a0
# CHECK-ERROR: immediate must be an integer in the range [0, 31]

cv.clip t0, 0, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.clip 0, t1, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.clip t0, t1
# CHECK-ERROR: too few operands for instruction

cv.clip t0, t1, 0, 0
# CHECK-ERROR: invalid operand for instruction

cv.addunr t0, t1, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.addunr t0, 0, t2
# CHECK-ERROR: register must be GPR (x0-x31)

cv.addunr 0, t1, t2
# CHECK-ERROR: register must be GPR (x0-x31)

cv.addunr t0, t1
# CHECK-ERROR: too few operands for instruction

cv.addunr t0, t1, t2, a0
# CHECK-ERROR: invalid operand for instruction

cv.addurn t0, t1, t2, -1
# CHECK-ERROR: immediate must be an integer in the range [0, 31]

cv.addurn t0, t1, t2, 32
# CHECK-ERROR: immediate must be an integer in the range [0, 31]

cv.addurn t0, t1, t2, a0
# CHECK-ERROR: immediate must be an integer in the range [0, 31]

cv.addurn t0, t1, 0, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.addurn t0, 0, t2, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.addurn 0, t1, t2, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.addurn t0, t1, t2
# CHECK-ERROR: too few operands for instruction

cv.addurn t0, t1, t2, 0, a0
# CHECK-ERROR: invalid operand for instruction

cv.subun t0, t1, t2, -1
# CHECK-ERROR: immediate must be an integer in the range [0, 31]

cv.subun t0, t1, t2, 32
# CHECK-ERROR: immediate must be an integer in the range [0, 31]

cv.subun t0, t1, t2, a0
# CHECK-ERROR: immediate must be an integer in the range [0, 31]

cv.subun t0, t1, 0, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.subun t0, 0, t2, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.subun 0, t1, t2, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.subun t0, t1, t2
# CHECK-ERROR: too few operands for instruction

cv.subun t0, t1, t2, 0, a0
# CHECK-ERROR: invalid operand for instruction

cv.subn t0, t1, t2, -1
# CHECK-ERROR: immediate must be an integer in the range [0, 31]

cv.subn t0, t1, t2, 32
# CHECK-ERROR: immediate must be an integer in the range [0, 31]

cv.subn t0, t1, t2, a0
# CHECK-ERROR: immediate must be an integer in the range [0, 31]

cv.subn t0, t1, 0, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.subn t0, 0, t2, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.subn 0, t1, t2, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.subn t0, t1, t2
# CHECK-ERROR: too few operands for instruction

cv.subn t0, t1, t2, 0, a0
# CHECK-ERROR: invalid operand for instruction

cv.subrnr t0, t1, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.subrnr t0, 0, t2
# CHECK-ERROR: register must be GPR (x0-x31)

cv.subrnr 0, t1, t2
# CHECK-ERROR: register must be GPR (x0-x31)

cv.subrnr t0, t1
# CHECK-ERROR: too few operands for instruction

cv.subrnr t0, t1, t2, a0
# CHECK-ERROR: invalid operand for instruction

cv.slet t0, t1, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.slet t0, 0, t2
# CHECK-ERROR: register must be GPR (x0-x31)

cv.slet 0, t1, t2
# CHECK-ERROR: register must be GPR (x0-x31)

cv.slet t0, t1
# CHECK-ERROR: too few operands for instruction

cv.slet t0, t1, t2, a0
# CHECK-ERROR: invalid operand for instruction

cv.suburnr t0, t1, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.suburnr t0, 0, t2
# CHECK-ERROR: register must be GPR (x0-x31)

cv.suburnr 0, t1, t2
# CHECK-ERROR: register must be GPR (x0-x31)

cv.suburnr t0, t1
# CHECK-ERROR: too few operands for instruction

cv.suburnr t0, t1, t2, a0
# CHECK-ERROR: invalid operand for instruction

cv.maxu t0, t1, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.maxu t0, 0, t2
# CHECK-ERROR: register must be GPR (x0-x31)

cv.maxu 0, t1, t2
# CHECK-ERROR: register must be GPR (x0-x31)

cv.maxu t0, t1
# CHECK-ERROR: too few operands for instruction

cv.maxu t0, t1, t2, a0
# CHECK-ERROR: invalid operand for instruction

cv.extbs t0, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.extbs 0, t1
# CHECK-ERROR: register must be GPR (x0-x31)

cv.extbs t0
# CHECK-ERROR: too few operands for instruction

cv.extbs t0, t1, t2
# CHECK-ERROR: invalid operand for instruction

cv.exths t0, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.exths 0, t1
# CHECK-ERROR: register must be GPR (x0-x31)

cv.exths t0
# CHECK-ERROR: too few operands for instruction

cv.exths t0, t1, t2
# CHECK-ERROR: invalid operand for instruction

cv.max t0, t1, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.max t0, 0, t2
# CHECK-ERROR: register must be GPR (x0-x31)

cv.max 0, t1, t2
# CHECK-ERROR: register must be GPR (x0-x31)

cv.max t0, t1
# CHECK-ERROR: too few operands for instruction

cv.max t0, t1, t2, a0
# CHECK-ERROR: invalid operand for instruction

cv.subunr t0, t1, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.subunr t0, 0, t2
# CHECK-ERROR: register must be GPR (x0-x31)

cv.subunr 0, t1, t2
# CHECK-ERROR: register must be GPR (x0-x31)

cv.subunr t0, t1
# CHECK-ERROR: too few operands for instruction

cv.subunr t0, t1, t2, a0
# CHECK-ERROR: invalid operand for instruction

cv.exthz t0, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.exthz 0, t1
# CHECK-ERROR: register must be GPR (x0-x31)

cv.exthz t0
# CHECK-ERROR: too few operands for instruction

cv.exthz t0, t1, t2
# CHECK-ERROR: invalid operand for instruction

cv.clipur t0, t1, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.clipur t0, 0, t2
# CHECK-ERROR: register must be GPR (x0-x31)

cv.clipur 0, t1, t2
# CHECK-ERROR: register must be GPR (x0-x31)

cv.clipur t0, t1
# CHECK-ERROR: too few operands for instruction

cv.clipur t0, t1, t2, a0
# CHECK-ERROR: invalid operand for instruction

cv.addurnr t0, t1, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.addurnr t0, 0, t2
# CHECK-ERROR: register must be GPR (x0-x31)

cv.addurnr 0, t1, t2
# CHECK-ERROR: register must be GPR (x0-x31)

cv.addurnr t0, t1
# CHECK-ERROR: too few operands for instruction

cv.addurnr t0, t1, t2, a0
# CHECK-ERROR: invalid operand for instruction

cv.addn t0, t1, t2, -1
# CHECK-ERROR: immediate must be an integer in the range [0, 31]

cv.addn t0, t1, t2, 32
# CHECK-ERROR: immediate must be an integer in the range [0, 31]

cv.addn t0, t1, t2, a0
# CHECK-ERROR: immediate must be an integer in the range [0, 31]

cv.addn t0, t1, 0, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.addn t0, 0, t2, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.addn 0, t1, t2, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.addn t0, t1, t2
# CHECK-ERROR: too few operands for instruction

cv.addn t0, t1, t2, 0, a0
# CHECK-ERROR: invalid operand for instruction

cv.subrn t0, t1, t2, -1
# CHECK-ERROR: immediate must be an integer in the range [0, 31]

cv.subrn t0, t1, t2, 32
# CHECK-ERROR: immediate must be an integer in the range [0, 31]

cv.subrn t0, t1, t2, a0
# CHECK-ERROR: immediate must be an integer in the range [0, 31]

cv.subrn t0, t1, 0, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.subrn t0, 0, t2, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.subrn 0, t1, t2, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.subrn t0, t1, t2
# CHECK-ERROR: too few operands for instruction

cv.subrn t0, t1, t2, 0, a0
# CHECK-ERROR: invalid operand for instruction

cv.subnr t0, t1, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.subnr t0, 0, t2
# CHECK-ERROR: register must be GPR (x0-x31)

cv.subnr 0, t1, t2
# CHECK-ERROR: register must be GPR (x0-x31)

cv.subnr t0, t1
# CHECK-ERROR: too few operands for instruction

cv.subnr t0, t1, t2, a0
# CHECK-ERROR: invalid operand for instruction

cv.clipr t0, t1, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.clipr t0, 0, t2
# CHECK-ERROR: register must be GPR (x0-x31)

cv.clipr 0, t1, t2
# CHECK-ERROR: register must be GPR (x0-x31)

cv.clipr t0, t1
# CHECK-ERROR: too few operands for instruction

cv.clipr t0, t1, t2, a0
# CHECK-ERROR: invalid operand for instruction

cv.sletu t0, t1, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.sletu t0, 0, t2
# CHECK-ERROR: register must be GPR (x0-x31)

cv.sletu 0, t1, t2
# CHECK-ERROR: register must be GPR (x0-x31)

cv.sletu t0, t1
# CHECK-ERROR: too few operands for instruction

cv.sletu t0, t1, t2, a0
# CHECK-ERROR: invalid operand for instruction

cv.min t0, t1, 0
# CHECK-ERROR: register must be GPR (x0-x31)

cv.min t0, 0, t2
# CHECK-ERROR: register must be GPR (x0-x31)

cv.min 0, t1, t2
# CHECK-ERROR: register must be GPR (x0-x31)

cv.min t0, t1
# CHECK-ERROR: too few operands for instruction

cv.min t0, t1, t2, a0
# CHECK-ERROR: invalid operand for instruction
