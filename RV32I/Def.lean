import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.FinCases

/-! # Chapter 2. Inst Base Integer Instruction Set, Version 2.1

## Chapter 34. RV32/64G Instruction Set Listings
The [ascii doc source](https://github.com/riscv/riscv-isa-manual/blob/main/src/rv-32-64g.adoc).

-/

/-! ## 2.1. Programmers' Model for Base Integer ISA
-/

inductive Reg
  /-- Zero. Immutable. -/
  | zero
  /-- Return address. -/
  | ra
  /-- Stack pointer. Preserved across calls. -/
  | sp
  /-- Global pointer. Unallocatable. -/
  | gp
  /-- Thread pointer. Unallocatable. -/
  | tp
  /-- Temporary registers. -/
  | t (i : Fin 7)
  /-- Callee-saved registers. Preserved across calls. -/
  | s (i : Fin 12)
  /-- Argument registers. -/
  | a (i : Fin 8)

instance Reg.x : Equiv (Fin 32) Reg where
  toFun
  -- := ![
  --   zero, ra, sp, gp, tp, t 0, t 1, t 2,
  --   s 0, s 1, a 0, a 1, a 2, a 3, a 4, a 5,
  --   a 6, a 7, s 2, s 3, s 4, s 5, s 6, s 7,
  --   s 8, s 9, s 10, s 11, t 3, t 4, t 5, t 6
  -- ]
    | 0 => zero | 1 => ra | 2 => sp | 3 => gp | 4 => tp
    | 5 => t 0 | 6 => t 1 | 7 => t 2
    | 8 => s 0 | 9 => s 1
    | 10 => a 0 | 11 => a 1 | 12 => a 2 | 13 => a 3 | 14 => a 4 | 15 => a 5
      | 16 => a 6 | 17 => a 7
    | 18 => s 2 | 19 => s 3 | 20 => s 4 | 21 => s 5 | 22 => s 6 | 23 => s 7
      | 24 => s 8 | 25 => s 9 | 26 => s 10 | 27 => s 11
    | 28 => t 3 | 29 => t 4 | 30 => t 5 | 31 => t 6
    | ⟨n + 32, (h : n + 32 < 32)⟩ =>
      absurd (Nat.le_add_left 32 n) (Nat.not_le_of_gt h)
  invFun
    | zero => 0 | ra => 1 | sp => 2 | gp => 3 | tp => 4
    | t 0 => 5 | t 1 => 6 | t 2 => 7
    | s 0 => 8 | s 1 => 9
    | a ⟨n, _⟩ => n + 10
    | s ⟨n + 2, _⟩ => n + 18
    -- | t 3 => 28 | t 4 => 29 | t 5 => 30 | t 6 => 31
    | t ⟨n + 3, _⟩ => n + 28
  left_inv (i : Fin 32) := by fin_cases i <;> rfl
  right_inv (x : Reg) := by
    cases x <;> try rfl
    case t i => fin_cases i <;> rfl
    case s i => fin_cases i <;> rfl
    case a i => fin_cases i <;> rfl

instance : Coe Reg (BitVec 5) where
  coe x := Reg.x.symm x

instance : Coe (BitVec 5) Reg where
  coe i := Reg.x i.toFin

/-- Table 70. RISC-V base opcode map, `inst[1:0]=11`. -/
inductive Opcode : Type
  -- `inst[6:5]=00`
  | LOAD | «LOAD-FP» | «custom-0» | «MISC-MEM» | «OP-IMM» | AUIPC | «OP-IMM-32» | «48b»
  -- `inst[6:5]=01`
  | STORE | «STORE-FP» | «custom-1» | AMO | OP | LUI | «OP-32» | «64b»
  -- `inst[6:5]=10`
  | MADD | MSUB | NMSUB | NMADD | «OP-FP» | «OP-V» | «custom-2/rv128»
    /-- Rewritten as `48b` in the spec. -/ | «48b'»
  -- `inst[6:5]=11`
  | BRANCH | JALR | reserved | JAL | SYSTEM | «OP-VE» | «custom-3/rv128» | «≥80b»

def Opcode.toBitVec : Opcode → BitVec 7
  -- `inst[6:5]=00`
  | LOAD             => 0b00_000_11
  | «LOAD-FP»        => 0b00_001_11
  | «custom-0»       => 0b00_010_11
  | «MISC-MEM»       => 0b00_011_11
  | «OP-IMM»         => 0b00_100_11
  | AUIPC            => 0b00_101_11
  | «OP-IMM-32»      => 0b00_110_11
  | «48b»            => 0b00_111_11
  -- `inst[6:5]=01`
  | STORE            => 0b01_000_11
  | «STORE-FP»       => 0b01_001_11
  | «custom-1»       => 0b01_010_11
  | AMO              => 0b01_011_11
  | OP               => 0b01_100_11
  | LUI              => 0b01_101_11
  | «OP-32»          => 0b01_110_11
  | «64b»            => 0b01_111_11
  -- `inst[6:5]=10`
  | MADD             => 0b10_000_11
  | MSUB             => 0b10_001_11
  | NMSUB            => 0b10_010_11
  | NMADD            => 0b10_011_11
  | «OP-FP»          => 0b10_100_11
  | «OP-V»           => 0b10_101_11
  | «custom-2/rv128» => 0b10_110_11
  | «48b'»           => 0b10_111_11
  -- `inst[6:5]=11`
  | BRANCH           => 0b11_000_11
  | JALR             => 0b11_001_11
  | reserved         => 0b11_010_11
  | JAL              => 0b11_011_11
  | SYSTEM           => 0b11_100_11
  | «OP-VE»          => 0b11_101_11
  | «custom-3/rv128» => 0b11_110_11
  | «≥80b»           => 0b11_111_11

instance : Coe Opcode (BitVec 7) where
  coe := Opcode.toBitVec

theorem Opcode.toBitVec_lsbs_all_one (opcode : Opcode)
  : opcode.toBitVec.extractLsb 1 0 = 0b11#2 := by cases opcode <;> trivial

/-- 2.2. Base Instruction Formats -/
class inductive Inst.Format
  | Rtype
    : (funct7       : BitVec  7)
    → (rs2          : BitVec  5)
    → (rs1          : BitVec  5)
    → (funct3       : BitVec  3)
    → (rd           : BitVec  5)
    → Opcode → Format
  | Itype
    : («imm[11:0]»  : BitVec 12)
    → (rs1          : BitVec  5)
    → (funct3       : BitVec  3)
    → (rd           : BitVec  5)
    → Opcode → Format
  | Stype
    : («imm[11:5]»  : BitVec  7)
    → (rs2          : BitVec  5)
    → (rs1          : BitVec  5)
    → (funct3       : BitVec  3)
    → («imm[4:0]»   : BitVec  5)
    → Opcode → Format
  | Btype
    : («imm[12]»    : BitVec  1)
    → («imm[10:5]»  : BitVec  6)
    → (rs2          : BitVec  5)
    → (rs1          : BitVec  5)
    → (funct3       : BitVec  3)
    → («imm[4:1]»   : BitVec  4)
    → («imm[11]»    : BitVec  1)
    → Opcode → Format
  | Utype
    : («imm[31:12]» : BitVec 20)
    → (rd           : BitVec  5)
    → Opcode → Format
  | Jtype
    : («imm[20]»    : BitVec  1)
    → («imm[10:1]»  : BitVec 10)
    → («imm[11]»    : BitVec  1)
    → («imm[19:12]» : BitVec  8)
    → (rd           : BitVec  5)
    → Opcode → Format

namespace Inst.Format

abbrev Rtype' funct7 rs2 rs1 funct3 rd :=
  Rtype funct7 rs2 rs1 funct3 rd .OP

/-- Shifts by a constant -/
abbrev Itype' (funct7 : BitVec 7) (shamt : BitVec 5) rs1 funct3 rd :=
  Itype (funct7 ++ shamt) rs1 funct3 rd .«OP-IMM»

/-- `pred,succ = iorw` -/
abbrev Mtype (fm pred succ : BitVec  4) rs1 funct3 rd :=
  Itype (fm ++ pred ++ succ) rs1 funct3 rd .«MISC-MEM»

abbrev Stype' (offset : BitVec 12) rs2 rs1 funct3 :=
  Stype
    (offset.extractLsb 11 5)
    rs2 rs1 funct3
    (offset.extractLsb  4 0)
    .STORE

abbrev Btype' (offset1 : BitVec 12) rs2 rs1 funct3 :=
  Btype
    (offset1.extractLsb 11 11)
    (offset1.extractLsb  9  4)
    rs2 rs1 funct3
    (offset1.extractLsb  3  0)
    (offset1.extractLsb 10 10)
    .BRANCH

abbrev Jtype' (offset1 : BitVec 20) rd :=
  Jtype
    (offset1.extractLsb 19 19)
    (offset1.extractLsb  9  0)
    (offset1.extractLsb 10 10)
    (offset1.extractLsb 18 11)
    rd .JAL

def toUInt32 : Format → UInt32
  | Rtype funct7 rs2 rs1 funct3 rd opcode =>
    UInt32.mk <| funct7 ++ rs2 ++ rs1 ++ funct3 ++ rd ++ opcode.toBitVec
  | Itype «imm[11:0]» rs1 funct3 rd opcode =>
    UInt32.mk <| «imm[11:0]» ++ rs1 ++ funct3 ++ rd ++ opcode.toBitVec
  | Stype «imm[11:5]» rs2 rs1 funct3 «imm[4:0]» opcode =>
    UInt32.mk <| «imm[11:5]» ++ rs2 ++ rs1 ++ funct3 ++ «imm[4:0]» ++ opcode.toBitVec
  | Btype «imm[12]» «imm[10:5]» rs2 rs1 funct3 «imm[4:1|11]» «imm[11]» opcode =>
    UInt32.mk <| «imm[12]» ++ «imm[10:5]» ++ rs2 ++ rs1 ++ funct3 ++ «imm[4:1|11]» ++ «imm[11]» ++ opcode.toBitVec
  | Utype «imm[31:12]» rd opcode =>
    UInt32.mk <| «imm[31:12]» ++ rd ++ opcode.toBitVec
  | Jtype «imm[20]» «imm[10:1]» «imm[11]» «imm[19:12]» rd opcode =>
    UInt32.mk <| «imm[20]» ++ «imm[10:1]» ++ «imm[11]» ++ «imm[19:12]» ++ rd ++ opcode.toBitVec

end Inst.Format

/-! ## 2.4. Integer Computational Instructions

No integer computational instructions cause arithmetic exceptions.
-/

inductive Inst
  /- 2.4.1. Integer Register-Immediate Instructions -/
  | ADDI  (rd rs1     : Reg) (imm   : BitVec 12)
  | SLTI  (rd rs1     : Reg) (imm   : BitVec 12)
  | SLTIU (rd rs1     : Reg) (imm   : BitVec 12)
  | ANDI  (rd rs1     : Reg) (imm   : BitVec 12)
  | ORI   (rd rs1     : Reg) (imm   : BitVec 12)
  | XORI  (rd rs1     : Reg) (imm   : BitVec 12)
  | SLLI  (rd rs1     : Reg) (shamt : BitVec  5)
  | SRLI  (rd rs1     : Reg) (shamt : BitVec  5)
  | SRAI  (rd rs1     : Reg) (shamt : BitVec  5)
  | LUI   (rd         : Reg) (imm   : BitVec 20)
  | AUIPC (rd         : Reg) (imm   : BitVec 20)
  /- 2.4.2. Integer Register-Register Operations -/
  | ADD   (rd rs1 rs2 : Reg)
  | SLT   (rd rs1 rs2 : Reg)
  | SLTU  (rd rs1 rs2 : Reg)
  | AND   (rd rs1 rs2 : Reg)
  | OR    (rd rs1 rs2 : Reg)
  | XOR   (rd rs1 rs2 : Reg)
  | SLL   (rd rs1 rs2 : Reg)
  | SRL   (rd rs1 rs2 : Reg)
  | SUB   (rd rs1 rs2 : Reg)
  | SRA   (rd rs1 rs2 : Reg)
  /- 2.5.1. Unconditional Jumps -/
  | JAL   (rd         : Reg) (offset : BitVec 20)
  | JALR  (rd rs1     : Reg) (offset : BitVec 12)
  /- 2.5.2. Conditional Branches -/
  | BEQ   (   rs1 rs2 : Reg) (offset : BitVec 12)
  | BNE   (   rs1 rs2 : Reg) (offset : BitVec 12)
  | BLT   (   rs1 rs2 : Reg) (offset : BitVec 12)
  | BGE   (   rs1 rs2 : Reg) (offset : BitVec 12)
  | BLTU  (   rs1 rs2 : Reg) (offset : BitVec 12)
  | BGEU  (   rs1 rs2 : Reg) (offset : BitVec 12)
  /- 2.6. Load and Store Instructions -/
  | LW    (rd rs1     : Reg) (offset : BitVec 12)
  | LH    (rd rs1     : Reg) (offset : BitVec 12)
  | LHU   (rd rs1     : Reg) (offset : BitVec 12)
  | LB    (rd rs1     : Reg) (offset : BitVec 12)
  | LBU   (rd rs1     : Reg) (offset : BitVec 12)
  | SW   (rs2 rs1     : Reg) (offset : BitVec 12)
  | SH   (rs2 rs1     : Reg) (offset : BitVec 12)
  | SB   (rs2 rs1     : Reg) (offset : BitVec 12)
  /- 2.7. Memory Ordering Instructions -/
  | FENCE (pred succ : BitVec 4)
  | FENCE.TSO
  /- 2.8. Environment Call and Breakpoints -/
  | ECALL
  | EBREAK

namespace Inst

instance toFormat : Inst → Format
  /- 2.4.1. Integer Register-Immediate Instructions -/
  | ADDI  rd  rs1 imm    => .Itype  imm          rs1 0b000 rd .«OP-IMM»
  | SLTI  rd  rs1 imm    => .Itype  imm          rs1 0b010 rd .«OP-IMM»
  | SLTIU rd  rs1 imm    => .Itype  imm          rs1 0b011 rd .«OP-IMM»
  | ANDI  rd  rs1 imm    => .Itype  imm          rs1 0b111 rd .«OP-IMM»
  | ORI   rd  rs1 imm    => .Itype  imm          rs1 0b110 rd .«OP-IMM»
  | XORI  rd  rs1 imm    => .Itype  imm          rs1 0b100 rd .«OP-IMM»
  | SLLI  rd  rs1 shamt  => .Itype'      0 shamt rs1 0b001 rd
  | SRLI  rd  rs1 shamt  => .Itype'      0 shamt rs1 0b101 rd
  | SRAI  rd  rs1 shamt  => .Itype'     32 shamt rs1 0b101 rd
  | LUI   rd      imm    => .Utype  imm                    rd .LUI
  | AUIPC rd      imm    => .Utype  imm                    rd .AUIPC
  /- 2.4.2. Integer Register-Register Operations -/
  | ADD   rd  rs1 rs2    => .Rtype'      0 rs2   rs1 0b000 rd
  | SLT   rd  rs1 rs2    => .Rtype'      0 rs2   rs1 0b010 rd
  | SLTU  rd  rs1 rs2    => .Rtype'      0 rs2   rs1 0b011 rd
  | AND   rd  rs1 rs2    => .Rtype'      0 rs2   rs1 0b111 rd
  | OR    rd  rs1 rs2    => .Rtype'      0 rs2   rs1 0b110 rd
  | XOR   rd  rs1 rs2    => .Rtype'      0 rs2   rs1 0b100 rd
  | SLL   rd  rs1 rs2    => .Rtype'      0 rs2   rs1 0b001 rd
  | SRL   rd  rs1 rs2    => .Rtype'      0 rs2   rs1 0b101 rd
  | SUB   rd  rs1 rs2    => .Rtype'     32 rs2   rs1 0b000 rd
  | SRA   rd  rs1 rs2    => .Rtype'     32 rs2   rs1 0b101 rd
  /- 2.5.1. Unconditional Jumps -/
  | JAL   rd      offset => .Jtype' offset                 rd
  | JALR  rd  rs1 offset => .Itype  offset       rs1 0b000 rd .JALR
  /- 2.5.2. Conditional Branches -/
  | BEQ   rs1 rs2 offset => .Btype' offset rs2   rs1 0b000
  | BNE   rs1 rs2 offset => .Btype' offset rs2   rs1 0b001
  | BLT   rs1 rs2 offset => .Btype' offset rs2   rs1 0b100
  | BGE   rs1 rs2 offset => .Btype' offset rs2   rs1 0b101
  | BLTU  rs1 rs2 offset => .Btype' offset rs2   rs1 0b110
  | BGEU  rs1 rs2 offset => .Btype' offset rs2   rs1 0b111
  /- 2.6. Load and Store Instructions -/
  | LW    rd  rs1 offset => .Itype  offset       rs1 0b010 rd .LOAD
  | LH    rd  rs1 offset => .Itype  offset       rs1 0b001 rd .LOAD
  | LHU   rd  rs1 offset => .Itype  offset       rs1 0b101 rd .LOAD
  | LB    rd  rs1 offset => .Itype  offset       rs1 0b000 rd .LOAD
  | LBU   rd  rs1 offset => .Itype  offset       rs1 0b100 rd .LOAD
  | SW    rs2 rs1 offset => .Stype' offset rs2   rs1 0b010
  | SH    rs2 rs1 offset => .Stype' offset rs2   rs1 0b001
  | SB    rs2 rs1 offset => .Stype' offset rs2   rs1 0b000
  /- 2.7. Memory Ordering Instructions -/
  | FENCE pred succ      => .Mtype 0 pred   succ   0 0b000  0
  | FENCE.TSO            => .Mtype 8 0b0011 0b0011 0 0b000  0
  /- 2.8. Environment Call and Breakpoints -/
  | ECALL                => .Itype              0  0 0b000  0 .SYSTEM
  | EBREAK               => .Itype              1  0 0b000  0 .SYSTEM

abbrev toUInt32 (inst : Inst) : UInt32 := inst.toFormat.toUInt32

namespace Pseudo

/-- `rd = rs1` -/
abbrev MOV rd rs1 := ADDI rd rs1 0
/-- `rd = if rs1 = 0 then 1 else 0` -/
abbrev SEQZ rd rs1 := SLTIU rd rs1 1
/-- `rd = ~~~rs1` -/
abbrev NOT rd rs1 := XORI rd rs1 (-1 : Int)
/-- `rd = if rs2 ≠ 0 then 1 else 0` -/
abbrev SNEZ rd rs2 := SLTU rd .zero rs2
/-- 2.4.3. NOP Instruction -/
abbrev NOP := ADDI .zero .zero 0
/-- Unconditional jump -/
abbrev J offset := JAL .zero offset

end Pseudo

namespace Hint

abbrev NTL.P1   := ADD .zero .zero (.x 2)
abbrev NTL.PALL := ADD .zero .zero (.x 3)
abbrev NTL.S1   := ADD .zero .zero (.x 4)
abbrev NTL.ALL  := ADD .zero .zero (.x 5)
abbrev PAUSE    := FENCE 0b0001 0b0000

end Hint

/-- Instruction decoder. -/
def fromUInt32 : UInt32 → Option Inst := fun ⟨op⟩ =>
  let funct7 : BitVec  7 := op.extractLsb 31 25
  let msbs12 : BitVec 12 := op.extractLsb 31 20
  let rs2    : BitVec  5 := op.extractLsb 24 20
  let rs1    : BitVec  5 := op.extractLsb 19 15
  let msbs20 : BitVec 20 := op.extractLsb 31 12
  let funct3 : BitVec  3 := op.extractLsb 14 12
  let rd     : BitVec  5 := op.extractLsb 11  7
  let opcode : BitVec  7 := op.extractLsb  6  0
  match opcode with
  | 0b1101111 =>
    let offset : BitVec 20 :=
      msbs20.extractLsb 19 19 ++ msbs20.extractLsb  7 0 ++
      msbs20.extractLsb  8  8 ++ msbs20.extractLsb 18 9
    JAL rd offset
  | 0b0110111 => LUI   rd msbs20
  | 0b0010111 => AUIPC rd msbs20
  | 0b1100011 =>
    let offset : BitVec 12 :=
      funct7.extractLsb 6 6 ++ rd.extractLsb 0 0 ++
      funct7.extractLsb 5 0 ++ rd.extractLsb 3 0
    match funct3 with
    | 0b000 => BEQ  rs1 rs2 offset
    | 0b001 => BNE  rs1 rs2 offset
    | 0b100 => BLT  rs1 rs2 offset
    | 0b101 => BGE  rs1 rs2 offset
    | 0b110 => BLTU rs1 rs2 offset
    | 0b111 => BGEU rs1 rs2 offset
    | _ => none
  | 0b0100011 =>
    let offset : BitVec 12 := funct7 ++ rd
    match funct3 with
    | 0b000 => SB rs1 rs2 offset
    | 0b001 => SH rs1 rs2 offset
    | 0b010 => SW rs1 rs2 offset
    | _ => none
  | 0b1100111 =>
    match funct3 with
    | 0b000 => JALR rs1 rd msbs12
    | _ => none
  | 0b0000011 =>
    match funct3 with
    | 0b000 => LB  rd rs1 msbs12
    | 0b001 => LH  rd rs1 msbs12
    | 0b010 => LW  rd rs1 msbs12
    | 0b100 => LBU rd rs1 msbs12
    | 0b101 => LHU rd rs1 msbs12
    | _ => none
  | 0b0001111 =>
    let fm   : BitVec 4 := msbs12.extractLsb 11 8
    let pred : BitVec 4 := msbs12.extractLsb  7 4
    let succ : BitVec 4 := msbs12.extractLsb  3 0
    match fm, pred, succ with
    | 0b1000, 0b0011, 0b0011 => FENCE.TSO
    | _, _, _ => FENCE pred succ
  | 0b1110011 =>
    match msbs12 with
    | 0 => ECALL
    | 1 => EBREAK
    | _ => none
  | 0b0010011 =>
    match funct3, funct7 with
    | 0b000,  _ => ADDI  rd rs1 msbs12
    | 0b001,  0 => SLLI  rd rs1 rs2
    | 0b010,  _ => SLTI  rd rs1 msbs12
    | 0b011,  _ => SLTIU rd rs1 msbs12
    | 0b100,  _ => XORI  rd rs1 msbs12
    | 0b101,  0 => SRLI  rd rs1 rs2
    | 0b101, 32 => SRAI  rd rs1 rs2
    | 0b110,  _ => ORI   rd rs1 msbs12
    | 0b111,  _ => ANDI  rd rs1 msbs12
    | _, _ => none
  | 0b0110011 =>
    match funct3, funct7 with
    | 0b000,  0 => ADD  rd rs1 rs2
    | 0b000, 32 => SUB  rd rs1 rs2
    | 0b001,  0 => SLL  rd rs1 rs2
    | 0b010,  0 => SLT  rd rs1 rs2
    | 0b011,  0 => SLTU rd rs1 rs2
    | 0b100,  0 => XOR  rd rs1 rs2
    | 0b101,  0 => SRL  rd rs1 rs2
    | 0b101, 32 => SRA  rd rs1 rs2
    | 0b110,  0 => OR   rd rs1 rs2
    | 0b111,  0 => AND  rd rs1 rs2
    | _, _ => none
  | _ => none

/-- The instruction decoder decodes all instructions. -/
@[simp]
theorem fromUInt32_complete : ∀ inst, fromUInt32 inst.toUInt32 = some inst :=
  sorry

/-- `Inst.fromUInt32_complete` in point-free convention. -/
example : fromUInt32 ∘ toUInt32 = some := funext fromUInt32_complete

example  {op inst} (h : fromUInt32 op = some inst) : inst.toUInt32 = op :=
  -- suffices some inst.toUInt32 = some op from Option.some_inj.mp this
  suffices _ from sorry
  calc fromUInt32 inst.toUInt32
    _ = some inst := inst.fromUInt32_complete
    _ = fromUInt32 op := h.symm

example {op} (h : fromUInt32 op = none) : ∀ inst : Inst, inst.toUInt32 ≠ op :=
  sorry

example op : if let some inst := fromUInt32 op then inst.toUInt32 = op else False :=
  sorry

example {op inst} : fromUInt32 op = some inst ↔ inst.toUInt32 = op :=
  sorry

end Inst
