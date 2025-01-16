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
  | ofRtype : Rtype funct7 rs2 rs1 funct3 rd opcode → Inst
  | ofItype : Itype «imm[11:0]» rs1 funct3 rd opcode → Inst
  | ofStype : Stype «imm[11:5]» rs2 rs1 funct3 «imm[4:0]» opcode → Inst
  | ofBtype : Btype «imm[12|10:5]» rs2 rs1 funct3 «imm[4:1|11]» opcode → Inst
  | ofUtype : Utype «imm[31:12]» rd opcode → Inst
  | ofJtype : Jtype «imm[20|10:1|11|19:12]» rd opcode → Inst
