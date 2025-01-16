/-
file:///Users/learningstud/Downloads/unpriv-isa-asciidoc_20240411%20(1).pdf
-/

def XLEN := 32

inductive Register
  | x0
  | x1  (value : UInt32)
  | x2  (value : UInt32)
  | x3  (value : UInt32)
  | x4  (value : UInt32)
  | x5  (value : UInt32)
  | x6  (value : UInt32)
  | x7  (value : UInt32)
  | x8  (value : UInt32)
  | x9  (value : UInt32)
  | x10 (value : UInt32)
  | x11 (value : UInt32)
  | x12 (value : UInt32)
  | x13 (value : UInt32)
  | x14 (value : UInt32)
  | x15 (value : UInt32)
  | x16 (value : UInt32)
  | x17 (value : UInt32)
  | x18 (value : UInt32)
  | x19 (value : UInt32)
  | x20 (value : UInt32)
  | x21 (value : UInt32)
  | x22 (value : UInt32)
  | x23 (value : UInt32)
  | x24 (value : UInt32)
  | x25 (value : UInt32)
  | x26 (value : UInt32)
  | x27 (value : UInt32)
  | x28 (value : UInt32)
  | x29 (value : UInt32)
  | x30 (value : UInt32)
  | x31 (value : UInt32)
  | pc  (value : UInt32)

def IALIGN := 32

class Inst (α) where
  opcode : α → BitVec 7
  toUInt32 : α → UInt32

class ImmInst (α) extends Inst α where
  imm : α → UInt32

-- LSB to MSB
structure InstR where
  opcode : BitVec 7
  rd : BitVec 5
  funct3 : BitVec 3
  rs1 : BitVec 5
  rs2 : BitVec 5
  funct7 : BitVec 7

instance : Inst InstR where
  opcode i := i.opcode
  toUInt32 i := UInt32.mk <|
    i.funct7 ++ i.rs2 ++ i.rs1 ++ i.funct3 ++ i.rd ++ i.opcode

structure InstI where
  opcode : BitVec 7
  rd : BitVec 5
  funct3 : BitVec 3
  rs1 : BitVec 5
  «imm[11:0]»: BitVec 12

instance : ImmInst InstI where
  opcode i := i.opcode
  toUInt32 i := UInt32.mk <|
    i.«imm[11:0]» ++ i.rs1 ++ i.funct3 ++ i.rd ++ i.opcode
  imm i := UInt32.mk <| BitVec.setWidth' (by trivial) <|
    i.«imm[11:0]»

structure InstS where
  opcode : BitVec 7
  «imm[4:0]» : BitVec 5
  funct3 : BitVec 3
  rs1 : BitVec 5
  rs2 : BitVec 5
  «imm[11:5]» : BitVec 7

instance : ImmInst InstS where
  opcode i := i.opcode
  toUInt32 i := UInt32.mk <|
    i.«imm[11:5]» ++ i.rs2 ++ i.rs1 ++ i.funct3 ++ i.«imm[4:0]» ++ i.opcode
  imm i := UInt32.mk <| BitVec.setWidth' (by trivial) <|
    i.«imm[11:5]» ++ i.«imm[4:0]»

structure InstB where
  opcode : BitVec 7
  «imm[11]» : BitVec 1
  «imm[4:1]» : BitVec 4
  funct3 : BitVec 3
  rs1 : BitVec 5
  rs2 : BitVec 5
  «imm[10:5]» : BitVec 6
  «imm[12]» : BitVec 1

instance : ImmInst InstB where
  opcode i := i.opcode
  toUInt32 i := UInt32.mk <|
    i.«imm[12]» ++ i.«imm[10:5]» ++ i.rs2 ++ i.rs1 ++ i.funct3 ++ i.«imm[4:1]» ++ i.«imm[11]» ++ i.opcode
  imm i := UInt32.mk <| BitVec.setWidth' (by trivial) <|
    i.«imm[12]» ++ i.«imm[11]» ++ i.«imm[10:5]» ++ i.«imm[4:1]» ++ 0#1

structure InstU where
  opcode : BitVec 7
  rd : BitVec 5
  «imm[31:12]» : BitVec 20

instance : ImmInst InstU where
  opcode i := i.opcode
  toUInt32 i := UInt32.mk <|
    i.«imm[31:12]» ++ i.rd ++ i.opcode
  imm i := UInt32.mk <|
    i.«imm[31:12]».shiftLeftZeroExtend 12

structure InstJ where
  opcode : BitVec 7
  rd : BitVec 5
  «imm[19:12]» : BitVec 8
  «imm[11]» : BitVec 1
  «imm[10:1]» : BitVec 10
  «imm[20]» : BitVec 1

instance : ImmInst InstJ where
  opcode i := i.opcode
  toUInt32 i := UInt32.mk <|
    i.«imm[20]» ++ i.«imm[10:1]» ++ i.«imm[11]» ++ i.«imm[19:12]» ++ i.rd ++ i.opcode
  imm i := UInt32.mk <| BitVec.setWidth' (by trivial) <|
    i.«imm[20]» ++ i.«imm[19:12]» ++ i.«imm[11]» ++ i.«imm[10:1]» ++ 0#1

inductive Op
  | addi (rd : BitVec 5) (rs1 : BitVec 5) (imm : BitVec 12)
