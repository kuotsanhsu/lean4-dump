inductive Reg
inductive Imm

structure InstR (funct7 : BitVec 7) (funct3 : BitVec 3) where
  rs2 : Reg
  rs1 : Reg
  rd : Reg

structure InstI (funct3 : BitVec 3) where
  imm : BitVec 12
  rs1 : Reg
  rd : Reg

structure InstS (funct3 : BitVec 3) where
  imm : BitVec 12
  rs2 : Reg
  rs1 : Reg

structure InstB (funct3 : BitVec 3) where
  imm : BitVec 12
  rs2 : Reg
  rs1 : Reg

structure InstU where
  imm : BitVec 20
  rd : Reg

structure InstJ where
  imm : BitVec 20
  rd : Reg

inductive Inst : BitVec 7 → Type
  | lui   : InstU        → Inst 0x37
  | auipc : InstU        → Inst 0x17
  | jal   : InstJ        → Inst 0x6f
  | jalr  : InstI 0      → Inst 0x67
  | beq   : InstB 0      → Inst 0x63
  | bne   : InstB 1      → Inst 0x63
  | blt   : InstB 4      → Inst 0x63
  | bge   : InstB 5      → Inst 0x63
  | bltu  : InstB 6      → Inst 0x63
  | bgeu  : InstB 7      → Inst 0x63
  | lb    : InstI 0      → Inst 0x03
  | lh    : InstI 1      → Inst 0x03
  | lw    : InstI 2      → Inst 0x03
  | lbu   : InstI 4      → Inst 0x03
  | lhu   : InstI 5      → Inst 0x03
  | sb    : InstS 0      → Inst 0x23
  | sh    : InstS 1      → Inst 0x23
  | sw    : InstS 2      → Inst 0x23
  | addi  : InstI 0      → Inst 0x13
  | slti  : InstI 2      → Inst 0x13
  | SLTIU : InstI 3      → Inst 0x13
  | XORI  : InstI 4      → Inst 0x13
  | ORI   : InstI 6      → Inst 0x13
  | ANDI  : InstI 7      → Inst 0x13
  | SLLI  : InstI 1      → Inst 0x13
  | SRLI  : InstI 5      → Inst 0x13
  | SRAI  : InstI 5      → Inst 0x13 -- FIXME
  | ADD   : InstR 0 0    → Inst 0x33
  | SUB   : InstR 0 0x20 → Inst 0x33
  | SLL   : InstR 1 0    → Inst 0x33
  | SLT   : InstR 2 0    → Inst 0x33
  | SLTU  : InstR 3 0    → Inst 0x33
  | XOR   : InstR 4 0    → Inst 0x33
  | SRL   : InstR 5 0    → Inst 0x33
  | SRA   : InstR 5 0x20 → Inst 0x33
  | OR    : InstR 6 0    → Inst 0x33
  | AND   : InstR 7 0    → Inst 0x33
  | FENCE :                Inst 0x0f -- FIXME
  | FENCE.TSO :            Inst 0x0f -- FIXME
  | PAUSE :                Inst 0x0f -- FIXME
  | ecall :                Inst 0x73 -- FIXME
  | ebreak :               Inst 0x73 -- FIXME

/-- Table 70. RISC-V base opcode map, `inst[1:0]=11`. -/
inductive Opcode : («inst[6:5]» : BitVec 2) → («inst[4:2]» : BitVec 3) → Type
  -- `inst[6:5]=00`
  | LOAD             : Opcode 0b00 0b000
  | «LOAD-FP»        : Opcode 0b00 0b001
  | «custom-0»       : Opcode 0b00 0b010
  | «MISC-MEM»       : Opcode 0b00 0b011
  | «OP-IMM»         : Opcode 0b00 0b100
  | AUIPC            : Opcode 0b00 0b101
  | «OP-IMM-32»      : Opcode 0b00 0b110
  | «48b»            : Opcode 0b00 0b111
  -- `inst[6:5]=01`
  | STORE            : Opcode 0b01 0b000
  | «STORE-FP»       : Opcode 0b01 0b001
  | «custom-1»       : Opcode 0b01 0b010
  | AMO              : Opcode 0b01 0b011
  | OP               : Opcode 0b01 0b100
  | LUI              : Opcode 0b01 0b101
  | «OP-32»          : Opcode 0b01 0b110
  | «64b»            : Opcode 0b01 0b111
  -- `inst[6:5]=10`
  | MADD             : Opcode 0b01 0b000
  | MSUB             : Opcode 0b01 0b001
  | NMSUB            : Opcode 0b01 0b010
  | NMADD            : Opcode 0b01 0b011
  | «OP-FP»          : Opcode 0b01 0b100
  | «OP-V»           : Opcode 0b01 0b101
  | «custom-2/rv128» : Opcode 0b01 0b110
  /-- Rewritten as `48b` in the spec. -/
  | «48b'»           : Opcode 0b01 0b111
  -- `inst[6:5]=11`
  | BRANCH           : Opcode 0b11 0b000
  | JALR             : Opcode 0b11 0b001
  | reserved         : Opcode 0b11 0b010
  | JAL              : Opcode 0b11 0b011
  | SYSTEM           : Opcode 0b11 0b100
  | «OP-VE»          : Opcode 0b11 0b101
  | «custom-3/rv128» : Opcode 0b11 0b110
  | «≥80b»           : Opcode 0b11 0b111

instance Opcode.unique «inst[6:5]» «inst[4:2]» : Subsingleton (Opcode «inst[6:5]» «inst[4:2]») where
  allEq a b := sorry

def Opcode.toBitVec {«inst[6:5]» «inst[4:2]»} : Opcode «inst[6:5]» «inst[4:2]» → BitVec 7
  | _ => «inst[6:5]» ++ «inst[4:2]» ++ 0b11#2

theorem Opcode.toBitVec_lsbs_all_one {«inst[6:5]» «inst[4:2]»}
    (op : Opcode «inst[6:5]» «inst[4:2]») : op.toBitVec.extractLsb 1 0 = 0b11#2
:= congrArg BitVec.ofFin <| Fin.ext <|
  let lsbs : BitVec 5 := «inst[6:5]» ++ «inst[4:2]»
  let n := lsbs.toNat
  calc (lsbs ++ 3#2).toNat % 4
    _ = (n <<< 2 ||| 3) % 4 := congrArg (· % 4) <| lsbs.toNat_append 3
    _ = 3 &&& (n <<< 2 ||| 3) := sorry
    _ = 3 &&& n <<< 2 ||| 3 &&& 3 := Nat.and_or_distrib_left 3 (n <<< 2) 3
    _ = 0 ||| 3 &&& 3 := congrArg (· ||| 3) <|
      calc 3 &&& n <<< 2
        _ = 0 := sorry
