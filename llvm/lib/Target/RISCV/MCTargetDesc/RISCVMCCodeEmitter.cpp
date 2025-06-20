//===-- RISCVMCCodeEmitter.cpp - Convert RISC-V code to machine code ------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements the RISCVMCCodeEmitter class.
//
//===----------------------------------------------------------------------===//

#include "MCTargetDesc/RISCVBaseInfo.h"
#include "MCTargetDesc/RISCVFixupKinds.h"
#include "MCTargetDesc/RISCVMCAsmInfo.h"
#include "MCTargetDesc/RISCVMCTargetDesc.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/MC/MCAsmInfo.h"
#include "llvm/MC/MCCodeEmitter.h"
#include "llvm/MC/MCContext.h"
#include "llvm/MC/MCExpr.h"
#include "llvm/MC/MCInst.h"
#include "llvm/MC/MCInstBuilder.h"
#include "llvm/MC/MCInstrInfo.h"
#include "llvm/MC/MCRegisterInfo.h"
#include "llvm/MC/MCSubtargetInfo.h"
#include "llvm/MC/MCSymbol.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/Endian.h"
#include "llvm/Support/EndianStream.h"

using namespace llvm;

#define DEBUG_TYPE "mccodeemitter"

STATISTIC(MCNumEmitted, "Number of MC instructions emitted");
STATISTIC(MCNumFixups, "Number of MC fixups created");

namespace {
class RISCVMCCodeEmitter : public MCCodeEmitter {
  RISCVMCCodeEmitter(const RISCVMCCodeEmitter &) = delete;
  void operator=(const RISCVMCCodeEmitter &) = delete;
  MCContext &Ctx;
  MCInstrInfo const &MCII;

public:
  RISCVMCCodeEmitter(MCContext &ctx, MCInstrInfo const &MCII)
      : Ctx(ctx), MCII(MCII) {}

  ~RISCVMCCodeEmitter() override = default;

  void encodeInstruction(const MCInst &MI, SmallVectorImpl<char> &CB,
                         SmallVectorImpl<MCFixup> &Fixups,
                         const MCSubtargetInfo &STI) const override;

  void expandFunctionCall(const MCInst &MI, SmallVectorImpl<char> &CB,
                          SmallVectorImpl<MCFixup> &Fixups,
                          const MCSubtargetInfo &STI) const;

  void expandTLSDESCCall(const MCInst &MI, SmallVectorImpl<char> &CB,
                         SmallVectorImpl<MCFixup> &Fixups,
                         const MCSubtargetInfo &STI) const;

  void expandAddTPRel(const MCInst &MI, SmallVectorImpl<char> &CB,
                      SmallVectorImpl<MCFixup> &Fixups,
                      const MCSubtargetInfo &STI) const;

  void expandPseudoBccJump(const MCInst &MI, SmallVectorImpl<char> &CB,
                           SmallVectorImpl<MCFixup> &Fixups,
                           const MCSubtargetInfo &STI) const;

  void expandLongCondBr(const MCInst &MI, SmallVectorImpl<char> &CB,
                        SmallVectorImpl<MCFixup> &Fixups,
                        const MCSubtargetInfo &STI) const;

  void expandQCLongCondBrImm(const MCInst &MI, SmallVectorImpl<char> &CB,
                             SmallVectorImpl<MCFixup> &Fixups,
                             const MCSubtargetInfo &STI, unsigned Size) const;

  /// TableGen'erated function for getting the binary encoding for an
  /// instruction.
  uint64_t getBinaryCodeForInstr(const MCInst &MI,
                                 SmallVectorImpl<MCFixup> &Fixups,
                                 const MCSubtargetInfo &STI) const;

  /// Return binary encoding of operand. If the machine operand requires
  /// relocation, record the relocation and return zero.
  uint64_t getMachineOpValue(const MCInst &MI, const MCOperand &MO,
                             SmallVectorImpl<MCFixup> &Fixups,
                             const MCSubtargetInfo &STI) const;

  uint64_t getImmOpValueMinus1(const MCInst &MI, unsigned OpNo,
                               SmallVectorImpl<MCFixup> &Fixups,
                               const MCSubtargetInfo &STI) const;

  uint64_t getImmOpValueSlist(const MCInst &MI, unsigned OpNo,
                              SmallVectorImpl<MCFixup> &Fixups,
                              const MCSubtargetInfo &STI) const;

  template <unsigned N>
  unsigned getImmOpValueAsrN(const MCInst &MI, unsigned OpNo,
                             SmallVectorImpl<MCFixup> &Fixups,
                             const MCSubtargetInfo &STI) const;

  uint64_t getImmOpValue(const MCInst &MI, unsigned OpNo,
                         SmallVectorImpl<MCFixup> &Fixups,
                         const MCSubtargetInfo &STI) const;

  unsigned getVMaskReg(const MCInst &MI, unsigned OpNo,
                       SmallVectorImpl<MCFixup> &Fixups,
                       const MCSubtargetInfo &STI) const;

  unsigned getRlistOpValue(const MCInst &MI, unsigned OpNo,
                           SmallVectorImpl<MCFixup> &Fixups,
                           const MCSubtargetInfo &STI) const;

  unsigned getRlistS0OpValue(const MCInst &MI, unsigned OpNo,
                             SmallVectorImpl<MCFixup> &Fixups,
                             const MCSubtargetInfo &STI) const;
};
} // end anonymous namespace

MCCodeEmitter *llvm::createRISCVMCCodeEmitter(const MCInstrInfo &MCII,
                                              MCContext &Ctx) {
  return new RISCVMCCodeEmitter(Ctx, MCII);
}

// Expand PseudoCALL(Reg), PseudoTAIL and PseudoJump to AUIPC and JALR with
// relocation types. We expand those pseudo-instructions while encoding them,
// meaning AUIPC and JALR won't go through RISC-V MC to MC compressed
// instruction transformation. This is acceptable because AUIPC has no 16-bit
// form and C_JALR has no immediate operand field.  We let linker relaxation
// deal with it. When linker relaxation is enabled, AUIPC and JALR have a
// chance to relax to JAL.
// If the C extension is enabled, JAL has a chance relax to C_JAL.
void RISCVMCCodeEmitter::expandFunctionCall(const MCInst &MI,
                                            SmallVectorImpl<char> &CB,
                                            SmallVectorImpl<MCFixup> &Fixups,
                                            const MCSubtargetInfo &STI) const {
  MCInst TmpInst;
  MCOperand Func;
  MCRegister Ra;
  if (MI.getOpcode() == RISCV::PseudoTAIL) {
    Func = MI.getOperand(0);
    Ra = RISCVII::getTailExpandUseRegNo(STI.getFeatureBits());
  } else if (MI.getOpcode() == RISCV::PseudoCALLReg) {
    Func = MI.getOperand(1);
    Ra = MI.getOperand(0).getReg();
  } else if (MI.getOpcode() == RISCV::PseudoCALL) {
    Func = MI.getOperand(0);
    Ra = RISCV::X1;
  } else if (MI.getOpcode() == RISCV::PseudoJump) {
    Func = MI.getOperand(1);
    Ra = MI.getOperand(0).getReg();
  }
  uint32_t Binary;

  assert(Func.isExpr() && "Expected expression");

  const MCExpr *CallExpr = Func.getExpr();

  // Emit AUIPC Ra, Func with R_RISCV_CALL relocation type.
  TmpInst = MCInstBuilder(RISCV::AUIPC).addReg(Ra).addExpr(CallExpr);
  Binary = getBinaryCodeForInstr(TmpInst, Fixups, STI);
  support::endian::write(CB, Binary, llvm::endianness::little);

  if (MI.getOpcode() == RISCV::PseudoTAIL ||
      MI.getOpcode() == RISCV::PseudoJump)
    // Emit JALR X0, Ra, 0
    TmpInst = MCInstBuilder(RISCV::JALR).addReg(RISCV::X0).addReg(Ra).addImm(0);
  else
    // Emit JALR Ra, Ra, 0
    TmpInst = MCInstBuilder(RISCV::JALR).addReg(Ra).addReg(Ra).addImm(0);
  Binary = getBinaryCodeForInstr(TmpInst, Fixups, STI);
  support::endian::write(CB, Binary, llvm::endianness::little);
}

void RISCVMCCodeEmitter::expandTLSDESCCall(const MCInst &MI,
                                           SmallVectorImpl<char> &CB,
                                           SmallVectorImpl<MCFixup> &Fixups,
                                           const MCSubtargetInfo &STI) const {
  MCOperand SrcSymbol = MI.getOperand(3);
  assert(SrcSymbol.isExpr() &&
         "Expected expression as first input to TLSDESCCALL");
  const auto *Expr = dyn_cast<MCSpecifierExpr>(SrcSymbol.getExpr());
  MCRegister Link = MI.getOperand(0).getReg();
  MCRegister Dest = MI.getOperand(1).getReg();
  int64_t Imm = MI.getOperand(2).getImm();
  Fixups.push_back(
      MCFixup::create(0, Expr, ELF::R_RISCV_TLSDESC_CALL, MI.getLoc()));
  MCInst Call =
      MCInstBuilder(RISCV::JALR).addReg(Link).addReg(Dest).addImm(Imm);

  uint32_t Binary = getBinaryCodeForInstr(Call, Fixups, STI);
  support::endian::write(CB, Binary, llvm::endianness::little);
}

// Expand PseudoAddTPRel to a simple ADD with the correct relocation.
void RISCVMCCodeEmitter::expandAddTPRel(const MCInst &MI,
                                        SmallVectorImpl<char> &CB,
                                        SmallVectorImpl<MCFixup> &Fixups,
                                        const MCSubtargetInfo &STI) const {
  MCOperand DestReg = MI.getOperand(0);
  MCOperand SrcReg = MI.getOperand(1);
  MCOperand TPReg = MI.getOperand(2);
  assert(TPReg.isReg() && TPReg.getReg() == RISCV::X4 &&
         "Expected thread pointer as second input to TP-relative add");

  MCOperand SrcSymbol = MI.getOperand(3);
  assert(SrcSymbol.isExpr() &&
         "Expected expression as third input to TP-relative add");

  const auto *Expr = dyn_cast<MCSpecifierExpr>(SrcSymbol.getExpr());
  assert(Expr && Expr->getSpecifier() == ELF::R_RISCV_TPREL_ADD &&
         "Expected tprel_add relocation on TP-relative symbol");

  Fixups.push_back(
      MCFixup::create(0, Expr, ELF::R_RISCV_TPREL_ADD, MI.getLoc()));
  if (STI.hasFeature(RISCV::FeatureRelax))
    Fixups.back().setLinkerRelaxable();

  // Emit a normal ADD instruction with the given operands.
  MCInst TmpInst = MCInstBuilder(RISCV::ADD)
                       .addOperand(DestReg)
                       .addOperand(SrcReg)
                       .addOperand(TPReg);
  uint32_t Binary = getBinaryCodeForInstr(TmpInst, Fixups, STI);
  support::endian::write(CB, Binary, llvm::endianness::little);
}

static std::pair<unsigned, uint32_t> getBranchOpcodeAndWidth(unsigned PseudoOpcode) {
  switch (PseudoOpcode) {
  default:
    llvm_unreachable("Unexpected pesudo branch opcode!");
  case RISCV::PseudoBEQ_JAL:
  case RISCV::PseudoBEQ_QC_E_J:
    return {RISCV::BEQ, 4};
  case RISCV::PseudoBNE_JAL:
  case RISCV::PseudoBNE_QC_E_J:
    return {RISCV::BNE, 4};
  case RISCV::PseudoBLT_JAL:
  case RISCV::PseudoBLT_QC_E_J:
    return {RISCV::BLT, 4};
  case RISCV::PseudoBGE_JAL:
  case RISCV::PseudoBGE_QC_E_J:
    return {RISCV::BGE, 4};
  case RISCV::PseudoBLTU_JAL:
  case RISCV::PseudoBLTU_QC_E_J:
    return {RISCV::BLTU, 4};
  case RISCV::PseudoBGEU_JAL:
  case RISCV::PseudoBGEU_QC_E_J:
    return {RISCV::BGEU, 4};
  case RISCV::PseudoQC_BEQI_JAL:
  case RISCV::PseudoQC_BEQI_QC_E_J:
    return {RISCV::QC_BEQI, 4};
  case RISCV::PseudoQC_BNEI_JAL:
  case RISCV::PseudoQC_BNEI_QC_E_J:
      return {RISCV::QC_BNEI, 4};
  case RISCV::PseudoQC_BLTI_JAL:
  case RISCV::PseudoQC_BLTI_QC_E_J:
      return {RISCV::QC_BLTI, 4};
  case RISCV::PseudoQC_BGEI_JAL:
  case RISCV::PseudoQC_BGEI_QC_E_J:
      return {RISCV::QC_BGEI, 4};
  case RISCV::PseudoQC_BLTUI_JAL:
  case RISCV::PseudoQC_BLTUI_QC_E_J:
      return {RISCV::QC_BLTUI, 4};
  case RISCV::PseudoQC_BGEUI_JAL:
  case RISCV::PseudoQC_BGEUI_QC_E_J:
      return {RISCV::QC_BGEUI, 4};
  case RISCV::PseudoQC_E_BEQI_JAL:
  case RISCV::PseudoQC_E_BEQI_QC_E_J:
      return {RISCV::QC_E_BEQI, 6};
  case RISCV::PseudoQC_E_BNEI_JAL:
  case RISCV::PseudoQC_E_BNEI_QC_E_J:
      return {RISCV::QC_E_BNEI, 6};
  case RISCV::PseudoQC_E_BLTI_JAL:
  case RISCV::PseudoQC_E_BLTI_QC_E_J:
      return {RISCV::QC_E_BLTI, 6};
  case RISCV::PseudoQC_E_BGEI_JAL:
  case RISCV::PseudoQC_E_BGEI_QC_E_J:
      return {RISCV::QC_E_BGEI, 6};
  case RISCV::PseudoQC_E_BLTUI_JAL:
  case RISCV::PseudoQC_E_BLTUI_QC_E_J:
      return {RISCV::QC_E_BLTUI, 6};
  case RISCV::PseudoQC_E_BGEUI_JAL:
  case RISCV::PseudoQC_E_BGEUI_QC_E_J:
      return {RISCV::QC_E_BGEUI, 6};
  }
}

static std::tuple<unsigned, uint32_t, MCFixupKind> getJumpOpcodeAndWidth(unsigned PseudoOpcode) {
  switch (PseudoOpcode) {
  default:
    llvm_unreachable("Unexpected pesudo branch opcode!");
  case RISCV::PseudoBEQ_JAL:
  case RISCV::PseudoBNE_JAL:
  case RISCV::PseudoBLT_JAL:
  case RISCV::PseudoBGE_JAL:
  case RISCV::PseudoBLTU_JAL:
  case RISCV::PseudoBGEU_JAL:
  case RISCV::PseudoQC_BEQI_JAL:
  case RISCV::PseudoQC_BNEI_JAL:
  case RISCV::PseudoQC_BLTI_JAL:
  case RISCV::PseudoQC_BGEI_JAL:
  case RISCV::PseudoQC_BLTUI_JAL:
  case RISCV::PseudoQC_BGEUI_JAL:
  case RISCV::PseudoQC_E_BEQI_JAL:
  case RISCV::PseudoQC_E_BNEI_JAL:
  case RISCV::PseudoQC_E_BLTI_JAL:
  case RISCV::PseudoQC_E_BGEI_JAL:
  case RISCV::PseudoQC_E_BLTUI_JAL:
  case RISCV::PseudoQC_E_BGEUI_JAL:
    return {RISCV::JAL, 4, MCFixupKind(RISCV::fixup_riscv_jal)};
  case RISCV::PseudoBEQ_QC_E_J:
  case RISCV::PseudoBNE_QC_E_J:
  case RISCV::PseudoBLT_QC_E_J:
  case RISCV::PseudoBGE_QC_E_J:
  case RISCV::PseudoBLTU_QC_E_J:
  case RISCV::PseudoBGEU_QC_E_J:
  case RISCV::PseudoQC_BEQI_QC_E_J:
  case RISCV::PseudoQC_BNEI_QC_E_J:
  case RISCV::PseudoQC_BLTI_QC_E_J:
  case RISCV::PseudoQC_BGEI_QC_E_J:
  case RISCV::PseudoQC_BLTUI_QC_E_J:
  case RISCV::PseudoQC_BGEUI_QC_E_J:
  case RISCV::PseudoQC_E_BEQI_QC_E_J:
  case RISCV::PseudoQC_E_BNEI_QC_E_J:
  case RISCV::PseudoQC_E_BLTI_QC_E_J:
  case RISCV::PseudoQC_E_BGEI_QC_E_J:
  case RISCV::PseudoQC_E_BLTUI_QC_E_J:
  case RISCV::PseudoQC_E_BGEUI_QC_E_J:
    return {RISCV::QC_E_J, 6, MCFixupKind(RISCV::fixup_riscv_qc_e_call_plt)};
  }
}

static void maybeCompressBranch(unsigned &BranchOpcode, uint32_t &BranchSize, MCOperand &Src1, MCOperand &Src2) {
  if (BranchOpcode != RISCV::BEQ && BranchOpcode != RISCV::BNE)
    return;

  if (!Src1.isReg() || !Src2.isReg())
    return;

  MCRegister SrcReg1 = Src1.getReg();
  MCRegister SrcReg2 = Src2.getReg();

  unsigned NewOpcode = (BranchOpcode == RISCV::BEQ) ? RISCV::C_BEQZ : RISCV::C_BNEZ;

  if (RISCV::X8 <= SrcReg1.id() && SrcReg1.id() <= RISCV::X15 &&
      SrcReg2.id() == RISCV::X0) {
    BranchOpcode = NewOpcode;
    BranchSize = 2;
    return;
  }

  if (RISCV::X8 <= SrcReg2.id() && SrcReg2.id() <= RISCV::X15 &&
               SrcReg1.id() == RISCV::X0) {
    std::swap(Src1, Src2);
    BranchOpcode = NewOpcode;
    BranchSize = 2;
    return;
  }
}

// Expand Pseudo<Bcc>_<jump> into <Bcc> and <jump>. <Bcc> may get compressed.
void RISCVMCCodeEmitter::expandPseudoBccJump(const MCInst &MI,
                                            SmallVectorImpl<char> &CB,
                                            SmallVectorImpl<MCFixup> &Fixups,
                                            const MCSubtargetInfo &STI) const {
  unsigned PseudoOpcode = MI.getOpcode();
  MCOperand Src1 = MI.getOperand(0);
  MCOperand Src2 = MI.getOperand(1);
  MCOperand Dst = MI.getOperand(2);

  auto [BranchOpcode, BranchWidth] = getBranchOpcodeAndWidth(PseudoOpcode);
  auto [JumpOpcode, JumpWidth, JumpFixup] = getJumpOpcodeAndWidth(PseudoOpcode);

  if (STI.hasFeature(RISCV::FeatureStdExtZca))
    maybeCompressBranch(BranchOpcode, BranchWidth, Src1, Src2);

  auto NewBranch = MCInstBuilder(BranchOpcode)
    .addOperand(Src1);
  if (BranchOpcode != RISCV::C_BEQZ && BranchOpcode != RISCV::C_BNEZ)
    NewBranch.addOperand(Src2);
  NewBranch.addImm(BranchWidth + JumpWidth);
  uint64_t BranchBinary = getBinaryCodeForInstr(NewBranch, Fixups, STI);
  SmallVector<char, 8> BranchEncoding;
  support::endian::write(BranchEncoding, BranchBinary, llvm::endianness::little);
  BranchEncoding.truncate(BranchWidth);
  CB.append(BranchEncoding);

  // Save the number fixups.
  size_t FixupStartIndex = Fixups.size();

  auto NewJump = MCInstBuilder(JumpOpcode);
  if (JumpOpcode == RISCV::JAL)
    NewJump.addReg(RISCV::X0);
  NewJump.addOperand(Dst);
  uint64_t JumpBinary = getBinaryCodeForInstr(NewJump, Fixups, STI);
  SmallVector<char, 8> JumpEncoding;
  support::endian::write(JumpEncoding, JumpBinary, llvm::endianness::little);
  JumpEncoding.truncate(JumpWidth);
  CB.append(JumpEncoding);

  // Drop any fixup added so we can add the correct one.
  Fixups.resize(FixupStartIndex);

  if (Dst.isExpr()) {
    Fixups.push_back(MCFixup::create(BranchWidth, Dst.getExpr(), JumpFixup, MI.getLoc()));
  }
}

void RISCVMCCodeEmitter::encodeInstruction(const MCInst &MI,
                                           SmallVectorImpl<char> &CB,
                                           SmallVectorImpl<MCFixup> &Fixups,
                                           const MCSubtargetInfo &STI) const {
  const MCInstrDesc &Desc = MCII.get(MI.getOpcode());
  // Get byte count of instruction.
  unsigned Size = Desc.getSize();

  // RISCVInstrInfo::getInstSizeInBytes expects that the total size of the
  // expanded instructions for each pseudo is correct in the Size field of the
  // tablegen definition for the pseudo.
  switch (MI.getOpcode()) {
  default:
    break;
  case RISCV::PseudoCALLReg:
  case RISCV::PseudoCALL:
  case RISCV::PseudoTAIL:
  case RISCV::PseudoJump:
    expandFunctionCall(MI, CB, Fixups, STI);
    MCNumEmitted += 2;
    return;
  case RISCV::PseudoAddTPRel:
    expandAddTPRel(MI, CB, Fixups, STI);
    MCNumEmitted += 1;
    return;
  case RISCV::PseudoTLSDESCCall:
    expandTLSDESCCall(MI, CB, Fixups, STI);
    MCNumEmitted += 1;
    return;
  case RISCV::PseudoBEQ_JAL:
  case RISCV::PseudoBNE_JAL:
  case RISCV::PseudoBLT_JAL:
  case RISCV::PseudoBGE_JAL:
  case RISCV::PseudoBLTU_JAL:
  case RISCV::PseudoBGEU_JAL:
  case RISCV::PseudoQC_BEQI_JAL:
  case RISCV::PseudoQC_BNEI_JAL:
  case RISCV::PseudoQC_BLTI_JAL:
  case RISCV::PseudoQC_BGEI_JAL:
  case RISCV::PseudoQC_BLTUI_JAL:
  case RISCV::PseudoQC_BGEUI_JAL:
  case RISCV::PseudoQC_E_BEQI_JAL:
  case RISCV::PseudoQC_E_BNEI_JAL:
  case RISCV::PseudoQC_E_BLTI_JAL:
  case RISCV::PseudoQC_E_BGEI_JAL:
  case RISCV::PseudoQC_E_BLTUI_JAL:
  case RISCV::PseudoQC_E_BGEUI_JAL:
  case RISCV::PseudoBEQ_QC_E_J:
  case RISCV::PseudoBNE_QC_E_J:
  case RISCV::PseudoBLT_QC_E_J:
  case RISCV::PseudoBGE_QC_E_J:
  case RISCV::PseudoBLTU_QC_E_J:
  case RISCV::PseudoBGEU_QC_E_J:
  case RISCV::PseudoQC_BEQI_QC_E_J:
  case RISCV::PseudoQC_BNEI_QC_E_J:
  case RISCV::PseudoQC_BLTI_QC_E_J:
  case RISCV::PseudoQC_BGEI_QC_E_J:
  case RISCV::PseudoQC_BLTUI_QC_E_J:
  case RISCV::PseudoQC_BGEUI_QC_E_J:
  case RISCV::PseudoQC_E_BEQI_QC_E_J:
  case RISCV::PseudoQC_E_BNEI_QC_E_J:
  case RISCV::PseudoQC_E_BLTI_QC_E_J:
  case RISCV::PseudoQC_E_BGEI_QC_E_J:
  case RISCV::PseudoQC_E_BLTUI_QC_E_J:
  case RISCV::PseudoQC_E_BGEUI_QC_E_J:
    expandPseudoBccJump(MI, CB, Fixups, STI);
    MCNumEmitted += 2;
    return;
  }


  switch (Size) {
  default:
    llvm_unreachable("Unhandled encodeInstruction length!");
  case 2: {
    uint16_t Bits = getBinaryCodeForInstr(MI, Fixups, STI);
    support::endian::write<uint16_t>(CB, Bits, llvm::endianness::little);
    break;
  }
  case 4: {
    uint32_t Bits = getBinaryCodeForInstr(MI, Fixups, STI);
    support::endian::write(CB, Bits, llvm::endianness::little);
    break;
  }
  case 6: {
    uint64_t Bits = getBinaryCodeForInstr(MI, Fixups, STI) & 0xffff'ffff'ffffu;
    SmallVector<char, 8> Encoding;
    support::endian::write(Encoding, Bits, llvm::endianness::little);
    assert(Encoding[6] == 0 && Encoding[7] == 0 &&
           "Unexpected encoding for 48-bit instruction");
    Encoding.truncate(6);
    CB.append(Encoding);
    break;
  }
  case 8: {
    uint64_t Bits = getBinaryCodeForInstr(MI, Fixups, STI);
    support::endian::write(CB, Bits, llvm::endianness::little);
    break;
  }
  }

  ++MCNumEmitted; // Keep track of the # of mi's emitted.
}

uint64_t
RISCVMCCodeEmitter::getMachineOpValue(const MCInst &MI, const MCOperand &MO,
                                      SmallVectorImpl<MCFixup> &Fixups,
                                      const MCSubtargetInfo &STI) const {

  if (MO.isReg())
    return Ctx.getRegisterInfo()->getEncodingValue(MO.getReg());

  if (MO.isImm())
    return MO.getImm();

  llvm_unreachable("Unhandled expression!");
  return 0;
}

uint64_t
RISCVMCCodeEmitter::getImmOpValueMinus1(const MCInst &MI, unsigned OpNo,
                                        SmallVectorImpl<MCFixup> &Fixups,
                                        const MCSubtargetInfo &STI) const {
  const MCOperand &MO = MI.getOperand(OpNo);

  if (MO.isImm()) {
    uint64_t Res = MO.getImm();
    return (Res - 1);
  }

  llvm_unreachable("Unhandled expression!");
  return 0;
}

uint64_t
RISCVMCCodeEmitter::getImmOpValueSlist(const MCInst &MI, unsigned OpNo,
                                       SmallVectorImpl<MCFixup> &Fixups,
                                       const MCSubtargetInfo &STI) const {
  const MCOperand &MO = MI.getOperand(OpNo);
  assert(MO.isImm() && "Slist operand must be immediate");

  uint64_t Res = MO.getImm();
  switch (Res) {
  case 0:
    return 0;
  case 1:
    return 1;
  case 2:
    return 2;
  case 4:
    return 3;
  case 8:
    return 4;
  case 16:
    return 5;
  case 15:
    return 6;
  case 31:
    return 7;
  default:
    llvm_unreachable("Unhandled Slist value!");
  }
}

template <unsigned N>
unsigned
RISCVMCCodeEmitter::getImmOpValueAsrN(const MCInst &MI, unsigned OpNo,
                                      SmallVectorImpl<MCFixup> &Fixups,
                                      const MCSubtargetInfo &STI) const {
  const MCOperand &MO = MI.getOperand(OpNo);

  if (MO.isImm()) {
    uint64_t Res = MO.getImm();
    assert((Res & ((1 << N) - 1)) == 0 && "LSB is non-zero");
    return Res >> N;
  }

  return getImmOpValue(MI, OpNo, Fixups, STI);
}

uint64_t RISCVMCCodeEmitter::getImmOpValue(const MCInst &MI, unsigned OpNo,
                                           SmallVectorImpl<MCFixup> &Fixups,
                                           const MCSubtargetInfo &STI) const {
  bool EnableRelax = STI.hasFeature(RISCV::FeatureRelax);
  const MCOperand &MO = MI.getOperand(OpNo);

  MCInstrDesc const &Desc = MCII.get(MI.getOpcode());
  unsigned MIFrm = RISCVII::getFormat(Desc.TSFlags);

  // If the destination is an immediate, there is nothing to do.
  if (MO.isImm())
    return MO.getImm();

  assert(MO.isExpr() &&
         "getImmOpValue expects only expressions or immediates");
  const MCExpr *Expr = MO.getExpr();
  MCExpr::ExprKind Kind = Expr->getKind();
  unsigned FixupKind = RISCV::fixup_riscv_invalid;
  bool RelaxCandidate = false;
  if (Kind == MCExpr::Specifier) {
    const auto *RVExpr = cast<MCSpecifierExpr>(Expr);
    FixupKind = RVExpr->getSpecifier();
    switch (RVExpr->getSpecifier()) {
    default:
      assert(FixupKind && FixupKind < FirstTargetFixupKind &&
             "invalid specifier");
      break;
    case ELF::R_RISCV_TPREL_ADD:
      // tprel_add is only used to indicate that a relocation should be emitted
      // for an add instruction used in TP-relative addressing. It should not be
      // expanded as if representing an actual instruction operand and so to
      // encounter it here is an error.
      llvm_unreachable(
          "ELF::R_RISCV_TPREL_ADD should not represent an instruction operand");
    case RISCV::S_LO:
      if (MIFrm == RISCVII::InstFormatI)
        FixupKind = RISCV::fixup_riscv_lo12_i;
      else if (MIFrm == RISCVII::InstFormatS)
        FixupKind = RISCV::fixup_riscv_lo12_s;
      else
        llvm_unreachable("VK_LO used with unexpected instruction format");
      RelaxCandidate = true;
      break;
    case ELF::R_RISCV_HI20:
      FixupKind = RISCV::fixup_riscv_hi20;
      RelaxCandidate = true;
      break;
    case RISCV::S_PCREL_LO:
      if (MIFrm == RISCVII::InstFormatI)
        FixupKind = RISCV::fixup_riscv_pcrel_lo12_i;
      else if (MIFrm == RISCVII::InstFormatS)
        FixupKind = RISCV::fixup_riscv_pcrel_lo12_s;
      else
        llvm_unreachable("VK_PCREL_LO used with unexpected instruction format");
      RelaxCandidate = true;
      break;
    case ELF::R_RISCV_PCREL_HI20:
      FixupKind = RISCV::fixup_riscv_pcrel_hi20;
      RelaxCandidate = true;
      break;
    case RISCV::S_TPREL_LO:
      if (MIFrm == RISCVII::InstFormatI)
        FixupKind = ELF::R_RISCV_TPREL_LO12_I;
      else if (MIFrm == RISCVII::InstFormatS)
        FixupKind = ELF::R_RISCV_TPREL_LO12_S;
      else
        llvm_unreachable("VK_TPREL_LO used with unexpected instruction format");
      RelaxCandidate = true;
      break;
    case ELF::R_RISCV_TPREL_HI20:
      RelaxCandidate = true;
      break;
    case ELF::R_RISCV_CALL_PLT:
      FixupKind = RISCV::fixup_riscv_call_plt;
      RelaxCandidate = true;
      break;
    case RISCV::S_QC_ABS20:
      FixupKind = RISCV::fixup_riscv_qc_abs20_u;
      RelaxCandidate = true;
      break;
    }
  } else if (Kind == MCExpr::SymbolRef || Kind == MCExpr::Binary) {
    // FIXME: Sub kind binary exprs have chance of underflow.
    if (MIFrm == RISCVII::InstFormatJ) {
      FixupKind = RISCV::fixup_riscv_jal;
    } else if (MIFrm == RISCVII::InstFormatB) {
      FixupKind = RISCV::fixup_riscv_branch;
    } else if (MIFrm == RISCVII::InstFormatCJ) {
      FixupKind = RISCV::fixup_riscv_rvc_jump;
    } else if (MIFrm == RISCVII::InstFormatCB) {
      FixupKind = RISCV::fixup_riscv_rvc_branch;
    } else if (MIFrm == RISCVII::InstFormatI) {
      FixupKind = RISCV::fixup_riscv_12_i;
    } else if (MIFrm == RISCVII::InstFormatQC_EB) {
      FixupKind = RISCV::fixup_riscv_qc_e_branch;
    } else if (MIFrm == RISCVII::InstFormatQC_EAI) {
      FixupKind = RISCV::fixup_riscv_qc_e_32;
      RelaxCandidate = true;
    } else if (MIFrm == RISCVII::InstFormatQC_EJ) {
      FixupKind = RISCV::fixup_riscv_qc_e_call_plt;
      RelaxCandidate = true;
    }
  }

  assert(FixupKind != RISCV::fixup_riscv_invalid && "Unhandled expression!");

  Fixups.push_back(MCFixup::create(0, Expr, FixupKind, MI.getLoc()));
  // If linker relaxation is enabled and supported by this relocation, set
  // a bit so that if fixup is unresolved, a R_RISCV_RELAX relocation will be
  // appended.
  if (EnableRelax && RelaxCandidate)
    Fixups.back().setLinkerRelaxable();
  ++MCNumFixups;

  return 0;
}

unsigned RISCVMCCodeEmitter::getVMaskReg(const MCInst &MI, unsigned OpNo,
                                         SmallVectorImpl<MCFixup> &Fixups,
                                         const MCSubtargetInfo &STI) const {
  MCOperand MO = MI.getOperand(OpNo);
  assert(MO.isReg() && "Expected a register.");

  switch (MO.getReg()) {
  default:
    llvm_unreachable("Invalid mask register.");
  case RISCV::V0:
    return 0;
  case RISCV::NoRegister:
    return 1;
  }
}

unsigned RISCVMCCodeEmitter::getRlistOpValue(const MCInst &MI, unsigned OpNo,
                                             SmallVectorImpl<MCFixup> &Fixups,
                                             const MCSubtargetInfo &STI) const {
  const MCOperand &MO = MI.getOperand(OpNo);
  assert(MO.isImm() && "Rlist operand must be immediate");
  auto Imm = MO.getImm();
  assert(Imm >= 4 && "EABI is currently not implemented");
  return Imm;
}
unsigned
RISCVMCCodeEmitter::getRlistS0OpValue(const MCInst &MI, unsigned OpNo,
                                      SmallVectorImpl<MCFixup> &Fixups,
                                      const MCSubtargetInfo &STI) const {
  const MCOperand &MO = MI.getOperand(OpNo);
  assert(MO.isImm() && "Rlist operand must be immediate");
  auto Imm = MO.getImm();
  assert(Imm >= 4 && "EABI is currently not implemented");
  assert(Imm != RISCVZC::RA && "Rlist operand must include s0");
  return Imm;
}

#include "RISCVGenMCCodeEmitter.inc"
