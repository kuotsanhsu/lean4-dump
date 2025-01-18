/-! # Chapter 34. RV32/64G Instruction Set Listings

The [ascii doc source](https://github.com/riscv/riscv-isa-manual/blob/main/src/rv-32-64g.adoc).

## RV32I Base Instruction Set

-/

inductive Rtype
  : (funct7 : BitVec 7)
  → (rs2    : BitVec 5)
  → (rs1    : BitVec 5)
  → (funct3 : BitVec 3)
  → (rd     : BitVec 5)
  → (opcode : BitVec 7)
  → Type
  | SLLI shamt rs1 rd : Rtype 0b0000000 shamt rs1 0b001 rd 0b0010011
  | SRLI shamt rs1 rd : Rtype 0b0000000 shamt rs1 0b101 rd 0b0010011
  | SRAI shamt rs1 rd : Rtype 0b0100000 shamt rs1 0b101 rd 0b0010011
  | ADD  rs2   rs1 rd : Rtype 0b0000000 rs2   rs1 0b000 rd 0b0110011
  | SUB  rs2   rs1 rd : Rtype 0b0100000 rs2   rs1 0b000 rd 0b0110011
  | SLL  rs2   rs1 rd : Rtype 0b0000000 rs2   rs1 0b001 rd 0b0110011
  | SLT  rs2   rs1 rd : Rtype 0b0000000 rs2   rs1 0b010 rd 0b0110011
  | SLTU rs2   rs1 rd : Rtype 0b0000000 rs2   rs1 0b011 rd 0b0110011
  | XOR  rs2   rs1 rd : Rtype 0b0000000 rs2   rs1 0b100 rd 0b0110011
  | SRL  rs2   rs1 rd : Rtype 0b0000000 rs2   rs1 0b101 rd 0b0110011
  | SRA  rs2   rs1 rd : Rtype 0b0100000 rs2   rs1 0b101 rd 0b0110011
  | OR   rs2   rs1 rd : Rtype 0b0000000 rs2   rs1 0b110 rd 0b0110011
  | AND  rs2   rs1 rd : Rtype 0b0000000 rs2   rs1 0b111 rd 0b0110011

inductive Itype
  : («imm[11:0]» : BitVec 12)
  → (rs1         : BitVec  5)
  → (funct3      : BitVec  3)
  → (rd          : BitVec  5)
  → (opcode      : BitVec  7)
  → Type
  | JALR  «imm[11:0]» rs1 rd : Itype «imm[11:0]» rs1 0b000 rd 0b1100111
  | LB    «imm[11:0]» rs1 rd : Itype «imm[11:0]» rs1 0b000 rd 0b0000011
  | LH    «imm[11:0]» rs1 rd : Itype «imm[11:0]» rs1 0b001 rd 0b0000011
  | LW    «imm[11:0]» rs1 rd : Itype «imm[11:0]» rs1 0b010 rd 0b0000011
  | LBU   «imm[11:0]» rs1 rd : Itype «imm[11:0]» rs1 0b100 rd 0b0000011
  | LHU   «imm[11:0]» rs1 rd : Itype «imm[11:0]» rs1 0b101 rd 0b0000011
  | ADDI  «imm[11:0]» rs1 rd : Itype «imm[11:0]» rs1 0b000 rd 0b0010011
  | SLTI  «imm[11:0]» rs1 rd : Itype «imm[11:0]» rs1 0b010 rd 0b0010011
  | SLTIU «imm[11:0]» rs1 rd : Itype «imm[11:0]» rs1 0b011 rd 0b0010011
  | XORI  «imm[11:0]» rs1 rd : Itype «imm[11:0]» rs1 0b100 rd 0b0010011
  | ORI   «imm[11:0]» rs1 rd : Itype «imm[11:0]» rs1 0b110 rd 0b0010011
  | ANDI  «imm[11:0]» rs1 rd : Itype «imm[11:0]» rs1 0b111 rd 0b0010011
  | FENCE (fm pred succ : BitVec 4) rs1 rd : Itype (fm ++ pred ++ succ) rs1 0b000 rd 0b0001111
  | FENCE.TSO : Itype (0b1000#4 ++ 0b0011#4 ++ 0b0011#4) 0b00000 0b000 0b00000 0b0001111
  | PAUSE     : Itype (0b0000#4 ++ 0b0001#4 ++ 0b0000#4) 0b00000 0b000 0b00000 0b0001111
  | ECALL     : Itype 0b000000000000 0b00000 0b000 0b00000 0b1110011
  | EBREAK    : Itype 0b000000000001 0b00000 0b000 0b00000 0b1110011

inductive Stype
  : («imm[11:5]» : BitVec 7)
  → (rs2         : BitVec 5)
  → (rs1         : BitVec 5)
  → (funct3      : BitVec 3)
  → («imm[4:0]»  : BitVec 5)
  → (opcode      : BitVec 7)
  → Type
  | SB «imm[11:5]» rs2 rs1 «imm[4:0]» : Stype «imm[11:5]» rs2 rs1 0b000 «imm[4:0]» 0b0100011
  | SH «imm[11:5]» rs2 rs1 «imm[4:0]» : Stype «imm[11:5]» rs2 rs1 0b001 «imm[4:0]» 0b0100011
  | SW «imm[11:5]» rs2 rs1 «imm[4:0]» : Stype «imm[11:5]» rs2 rs1 0b010 «imm[4:0]» 0b0100011

inductive Btype
  : («imm[12|10:5]» : BitVec 7)
  → (rs2            : BitVec 5)
  → (rs1            : BitVec 5)
  → (funct3         : BitVec 3)
  → («imm[4:1|11]»  : BitVec 5)
  → (opcode         : BitVec 7)
  → Type
  | BEQ  «imm[12|10:5]» rs2 rs1 «imm[4:1|11]» : Btype «imm[12|10:5]» rs2 rs1 0b000 «imm[4:1|11]» 0b1100011
  | BNE  «imm[12|10:5]» rs2 rs1 «imm[4:1|11]» : Btype «imm[12|10:5]» rs2 rs1 0b001 «imm[4:1|11]» 0b1100011
  | BLT  «imm[12|10:5]» rs2 rs1 «imm[4:1|11]» : Btype «imm[12|10:5]» rs2 rs1 0b100 «imm[4:1|11]» 0b1100011
  | BGE  «imm[12|10:5]» rs2 rs1 «imm[4:1|11]» : Btype «imm[12|10:5]» rs2 rs1 0b101 «imm[4:1|11]» 0b1100011
  | BLTU «imm[12|10:5]» rs2 rs1 «imm[4:1|11]» : Btype «imm[12|10:5]» rs2 rs1 0b110 «imm[4:1|11]» 0b1100011
  | BGEU «imm[12|10:5]» rs2 rs1 «imm[4:1|11]» : Btype «imm[12|10:5]» rs2 rs1 0b111 «imm[4:1|11]» 0b1100011

inductive Utype
  : («imm[31:12]» : BitVec 20)
  → (rd           : BitVec  5)
  → (opcode       : BitVec  7)
  → Type
  | LUI   «imm[31:12]» rd : Utype «imm[31:12]» rd 0b0110111
  | AUIPC «imm[31:12]» rd : Utype «imm[31:12]» rd 0b0010111

inductive Jtype
  : («imm[20|10:1|11|19:12]» : BitVec 20)
  → (rd                      : BitVec  5)
  → (opcode                  : BitVec  7)
  → Type
  | JAL «imm[20|10:1|11|19:12]» rd : Jtype «imm[20|10:1|11|19:12]» rd 0b1101111

inductive Inst
  | ofRtype {funct7 rs2 rs1 funct3 rd opcode}
    : Rtype funct7 rs2 rs1 funct3 rd opcode → Inst
  | ofItype {«imm[11:0]» rs1 funct3 rd opcode}
    : Itype «imm[11:0]» rs1 funct3 rd opcode → Inst
  | ofStype {«imm[11:5]» rs2 rs1 funct3 «imm[4:0]» opcode}
    : Stype «imm[11:5]» rs2 rs1 funct3 «imm[4:0]» opcode → Inst
  | ofBtype {«imm[12|10:5]» rs2 rs1 funct3 «imm[4:1|11]» opcode}
    : Btype «imm[12|10:5]» rs2 rs1 funct3 «imm[4:1|11]» opcode → Inst
  | ofUtype {«imm[31:12]» rd opcode}
    : Utype «imm[31:12]» rd opcode → Inst
  | ofJtype {«imm[20|10:1|11|19:12]» rd opcode}
    : Jtype «imm[20|10:1|11|19:12]» rd opcode → Inst

namespace Inst

open Rtype Itype Stype Btype Utype Jtype

def toUInt32 : Inst → UInt32
  | @ofRtype funct7 rs2 rs1 funct3 rd opcode _ =>
    UInt32.mk <| funct7 ++ rs2 ++ rs1 ++ funct3 ++ rd ++ opcode
  | @ofItype «imm[11:0]» rs1 funct3 rd opcode _ =>
    UInt32.mk <| «imm[11:0]» ++ rs1 ++ funct3 ++ rd ++ opcode
  | @ofStype «imm[11:5]» rs2 rs1 funct3 «imm[4:0]» opcode _ =>
    UInt32.mk <| «imm[11:5]» ++ rs2 ++ rs1 ++ funct3 ++ «imm[4:0]» ++ opcode
  | @ofBtype «imm[12|10:5]» rs2 rs1 funct3 «imm[4:1|11]» opcode _ =>
    UInt32.mk <| «imm[12|10:5]» ++ rs2 ++ rs1 ++ funct3 ++ «imm[4:1|11]» ++ opcode
  | @ofUtype «imm[31:12]» rd opcode _ =>
    UInt32.mk <| «imm[31:12]» ++ rd ++ opcode
  | @ofJtype  «imm[20|10:1|11|19:12]» rd opcode _ =>
    UInt32.mk <| «imm[20|10:1|11|19:12]» ++ rd ++ opcode

/-- Instruction decoder. -/
def fromUInt32 : UInt32 → Option Inst := fun ⟨op⟩ =>
  let funct7 : BitVec  7 := op.extractLsb' 25 _
  let msbs12 : BitVec 12 := op.extractLsb' 20 _
  let rs2    : BitVec  5 := op.extractLsb' 20 _
  let rs1    : BitVec  5 := op.extractLsb' 15 _
  let msbs20 : BitVec 20 := op.extractLsb' 12 _
  let funct3 : BitVec  3 := op.extractLsb' 12 _
  let rd     : BitVec  5 := op.extractLsb'  7 _
  let opcode : BitVec  7 := op.extractLsb'  0 _
  match opcode with
  | 0b1101111 => ofJtype <| JAL   msbs20 rd
  | 0b0110111 => ofUtype <| LUI   msbs20 rd
  | 0b0010111 => ofUtype <| AUIPC msbs20 rd
  | 0b1100011 =>
    match funct3 with
    | 0b000 => ofBtype <| BEQ  funct7 rs2 rs1 rd
    | 0b001 => ofBtype <| BNE  funct7 rs2 rs1 rd
    | 0b100 => ofBtype <| BLT  funct7 rs2 rs1 rd
    | 0b101 => ofBtype <| BGE  funct7 rs2 rs1 rd
    | 0b110 => ofBtype <| BLTU funct7 rs2 rs1 rd
    | 0b111 => ofBtype <| BGEU funct7 rs2 rs1 rd
    | _ => none
  | 0b0100011 =>
    match funct3 with
    | 0b000 => ofStype <| SB funct7 rs2 rs1 rd
    | 0b001 => ofStype <| SH funct7 rs2 rs1 rd
    | 0b010 => ofStype <| SW funct7 rs2 rs1 rd
    | _ => none
  | 0b1100111 =>
    match funct3 with
    | 0b000 => ofItype <| JALR msbs12 rs1 rd
    | _ => none
  | 0b0000011 =>
    match funct3 with
    | 0b000 => ofItype <| LB  msbs12 rs1 rd
    | 0b001 => ofItype <| LH  msbs12 rs1 rd
    | 0b010 => ofItype <| LW  msbs12 rs1 rd
    | 0b100 => ofItype <| LBU msbs12 rs1 rd
    | 0b101 => ofItype <| LHU msbs12 rs1 rd
    | _ => none
  | 0b0001111 =>
    let fm   : BitVec 4 := msbs12.extractLsb' 8 _
    let pred : BitVec 4 := msbs12.extractLsb' 4 _
    let succ : BitVec 4 := msbs12.extractLsb' 0 _
    match fm, pred, succ with
    | 0b0000, 0b0001, 0b0000 => ofItype PAUSE
    | 0b1000, 0b0011, 0b0011 => ofItype FENCE.TSO
    | _, _, _ => ofItype <| FENCE fm pred succ rs1 rd
  | 0b1110011 =>
    match msbs12 with
    | 0 => ofItype ECALL
    | 1 => ofItype EBREAK
    | _ => none
  | 0b0010011 =>
    match funct3 with
    | 0b000 => ofItype <| ADDI  msbs12 rs1 rd
    | 0b001 =>
      match funct7 with
      | 0b0000000 => ofRtype <| SLLI rs2 rs1 rd
      | _ => none
    | 0b010 => ofItype <| SLTI  msbs12 rs1 rd
    | 0b011 => ofItype <| SLTIU msbs12 rs1 rd
    | 0b100 => ofItype <| XORI  msbs12 rs1 rd
    | 0b101 =>
      match funct7 with
      | 0b0000000 => ofRtype <| SRLI rs2 rs1 rd
      | 0b0100000 => ofRtype <| SRAI rs2 rs1 rd
      | _ => none
    | 0b110 => ofItype <| ORI   msbs12 rs1 rd
    | 0b111 => ofItype <| ANDI  msbs12 rs1 rd
    | _ => none
  | 0b0110011 =>
    match funct3, funct7 with
    | 0b000, 0b0000000 => ofRtype <| ADD  rs2 rs1 rd
    | 0b000, 0b0100000 => ofRtype <| SUB  rs2 rs1 rd
    | 0b001, 0b0000000 => ofRtype <| SLL  rs2 rs1 rd
    | 0b010, 0b0000000 => ofRtype <| SLT  rs2 rs1 rd
    | 0b011, 0b0000000 => ofRtype <| SLTU rs2 rs1 rd
    | 0b100, 0b0000000 => ofRtype <| XOR  rs2 rs1 rd
    | 0b101, 0b0000000 => ofRtype <| SRL  rs2 rs1 rd
    | 0b101, 0b0100000 => ofRtype <| SRA  rs2 rs1 rd
    | 0b110, 0b0000000 => ofRtype <| OR   rs2 rs1 rd
    | 0b111, 0b0000000 => ofRtype <| AND  rs2 rs1 rd
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
