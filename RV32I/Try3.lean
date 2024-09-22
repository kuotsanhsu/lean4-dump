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
