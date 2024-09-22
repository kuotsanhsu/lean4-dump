inductive Reg
inductive Imm

/-- No SUBI?! -/
inductive OpImm : BitVec 3 → Type
  | ADDI : OpImm 0 | SLTI : OpImm 2 | SLTIU : OpImm 3
  | XORI : OpImm 4 | ORI : OpImm 6 | ANDI : OpImm 7
  | SLLI : OpImm 1 | SRLI : OpImm 5 | SRAI : OpImm 5

inductive Op : BitVec 3 → BitVec 7 → Type
  | ADD : Op 0 0 | SUB : Op 0 0x20
  | SLT : Op 2 0 | SLTU : Op 3 0
  | AND : Op 7 0 | OR : Op 6 0 | XOR : Op 4 0
  | SLL : Op 1 0 | SRL : Op 5 0
  | SRA : Op 5 0x20

inductive Branch : BitVec 3 → Type
  | BEQ : Branch 0 | BNE : Branch 1 | BLT : Branch 4 | BGE : Branch 5
  | BLTU : Branch 6 | BGEU : Branch 7

inductive MiscMem -- : BitVec 3 → Type
  | FENCE | FENCE.TSO | PAUSE

inductive System : BitVec 12 → Type
  | ECALL : System 0 | EBREAK : System 1

inductive Load : BitVec 3 → Type
  | LB : Load 0 | LH : Load 1 | LW : Load 2 | LBU : Load 4 | LHU : Load 5

inductive Store : BitVec 3 → Type
  | SB : Store 0 | SH : Store 1 | SW : Store 2

inductive Opcode : BitVec 7 → Type
  | OP_IMM {funct3} : OpImm funct3 → Opcode 0x13
  | LUI : Opcode 0x37 | AUIPC : Opcode 0x17
  | OP {funct3 funct7} : Op funct3 funct7 → Opcode 0x33
  | JAL : Opcode 0x6f | JALR : Opcode 0x67
  | BRANCH {funct3} : Branch funct3 → Opcode 0x63
  | LOAD {funct3} : Load funct3 → Opcode 0x03 | STORE {funct3} : Store funct3 → Opcode 0x23
  | MISC_MEM : MiscMem → Opcode 0x0f
  | SYSTEM {imm} : System imm → Opcode 0x73

inductive Inst : {opcode : BitVec 7} → Opcode opcode → Type
  | lui   (        rd : Reg) (imm : Imm) : Inst <| .LUI
  | auipc (        rd : Reg) (imm : Imm) : Inst <| .AUIPC
  | jal   (        rd : Reg) (imm : Imm) : Inst <| .JAL
  | jalr  (    rs1 rd : Reg) (imm : Imm) : Inst <| .JALR
  | beq   (rs2 rs1    : Reg) (imm : Imm) : Inst <| .BRANCH   .BEQ
  | bne   (rs2 rs1    : Reg) (imm : Imm) : Inst <| .BRANCH   .BNE
  | blt   (rs2 rs1    : Reg) (imm : Imm) : Inst <| .BRANCH   .BLT
  | bge   (rs2 rs1    : Reg) (imm : Imm) : Inst <| .BRANCH   .BGE
  | bltu  (rs2 rs1    : Reg) (imm : Imm) : Inst <| .BRANCH   .BLTU
  | bgeu  (rs2 rs1    : Reg) (imm : Imm) : Inst <| .BRANCH   .BGEU
  | lb    (    rs1 rd : Reg) (imm : Imm) : Inst <| .LOAD     .LB
  | lh    (    rs1 rd : Reg) (imm : Imm) : Inst <| .LOAD     .LH
  | lW    (    rs1 rd : Reg) (imm : Imm) : Inst <| .LOAD     .LW
  | lbu   (    rs1 rd : Reg) (imm : Imm) : Inst <| .LOAD     .LBU
  | lhu   (    rs1 rd : Reg) (imm : Imm) : Inst <| .LOAD     .LHU
  | sb    (rs2 rs1    : Reg) (imm : Imm) : Inst <| .STORE    .SB
  | sh    (rs2 rs1    : Reg) (imm : Imm) : Inst <| .STORE    .SH
  | sw    (rs2 rs1    : Reg) (imm : Imm) : Inst <| .STORE    .SW
  | addi  (    rs1 rd : Reg) (imm : Imm) : Inst <| .OP_IMM   .ADDI
  | slti  (    rs1 rd : Reg) (imm : Imm) : Inst <| .OP_IMM   .SLTI
  | sltiu (    rs1 rd : Reg) (imm : Imm) : Inst <| .OP_IMM   .SLTIU
  | xori  (    rs1 rd : Reg) (imm : Imm) : Inst <| .OP_IMM   .XORI
  | ori   (    rs1 rd : Reg) (imm : Imm) : Inst <| .OP_IMM   .ORI
  | andi  (    rs1 rd : Reg) (imm : Imm) : Inst <| .OP_IMM   .ANDI
  | slli  (    rs1 rd : Reg) (imm : Imm) : Inst <| .OP_IMM   .SLLI
  | srli  (    rs1 rd : Reg) (imm : Imm) : Inst <| .OP_IMM   .SRLI
  | srai  (    rs1 rd : Reg) (imm : Imm) : Inst <| .OP_IMM   .SRAI
  | add   (rs2 rs1 rd : Reg)             : Inst <| .OP       .ADD
  | sub   (rs2 rs1 rd : Reg)             : Inst <| .OP       .SUB
  | sll   (rs2 rs1 rd : Reg)             : Inst <| .OP       .SLL
  | slt   (rs2 rs1 rd : Reg)             : Inst <| .OP       .SLT
  | sltu  (rs2 rs1 rd : Reg)             : Inst <| .OP       .SLTU
  | xor   (rs2 rs1 rd : Reg)             : Inst <| .OP       .XOR
  | srl   (rs2 rs1 rd : Reg)             : Inst <| .OP       .SRL
  | sra   (rs2 rs1 rd : Reg)             : Inst <| .OP       .SRA
  | or    (rs2 rs1 rd : Reg)             : Inst <| .OP       .OR
  | and   (rs2 rs1 rd : Reg)             : Inst <| .OP       .AND
  | fence (    rs1 rd : Reg) (imm : Imm) : Inst <| .MISC_MEM .FENCE
  | fence.tso                            : Inst <| .MISC_MEM .FENCE.TSO
  | pause                                : Inst <| .MISC_MEM .PAUSE
  | ecall                                : Inst <| .SYSTEM   .ECALL
  | ebreak                               : Inst <| .SYSTEM   .EBREAK
