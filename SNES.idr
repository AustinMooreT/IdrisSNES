import Data.Bits
import Data.Vect



-- TODO finish formulating cpu details
data ArithmeticMode = Binary | Decimal
data Width = Sixteen | ThirtyTwo
data CpuMode : Type where
     EmulationMode : ArithmeticMode -> CpuMode
     StandardMode  : ArithmeticMode -> Width -> Width -> CpuMode

record Cpu where
       constructor MkCpu
       cpuMode     : CpuMode
       registerA   : Bits 8
       registerB   : Bits 8
       registerXHi : Bits 8
       registerXLo : Bits 8
       registerYHi : Bits 8
       registerYLo : Bits 8
       registerDHi : Bits 8
       registerDLo : Bits 8
       registerSHi : Bits 8
       registerSLo : Bits 8
       registerPHi : Bits 8
       registerPLo : Bits 8

-- Template MkCpu (registerA c) (registerB c) (registerXHi c) (registerXLo c) (registerYHi c) (registerYLo c)

defaultCpu : Cpu
defaultCpu = MkCpu (EmulationMode Binary) (intToBits 0) (intToBits 0) (intToBits 0) (intToBits 0) (intToBits 0) (intToBits 0) (intToBits 0) (intToBits 0) (intToBits 0) (intToBits 0) (intToBits 0) (intToBits 0)

setRegisterA : Bits 8 -> Cpu -> Cpu
setRegisterA d c = MkCpu (cpuMode c) d (registerB c) (registerXHi c) (registerXLo c) (registerYHi c) (registerYLo c) (registerDHi c) (registerDLo c) (registerSHi c) (registerSLo c) (registerPHi c) (registerPLo c)

setRegisterB : Bits 8 -> Cpu -> Cpu
setRegisterB d c = MkCpu (cpuMode c) (registerA c) d (registerXHi c) (registerXLo c) (registerYHi c) (registerYLo c) (registerDHi c) (registerDLo c) (registerSHi c) (registerSLo c) (registerPHi c) (registerPLo c)

setRegisterXHi : Bits 8 -> Cpu -> Cpu
setRegisterXHi d c = MkCpu (cpuMode c) (registerA c) (registerB c) d (registerXLo c) (registerYHi c) (registerYLo c) (registerDHi c) (registerDLo c) (registerSHi c) (registerSLo c) (registerPHi c) (registerPLo c)

setRegisterXLo : Bits 8 -> Cpu -> Cpu
setRegisterXLo d c = MkCpu (cpuMode c) (registerA c) (registerB c) (registerXHi c) d (registerYHi c) (registerYLo c) (registerDHi c) (registerDLo c) (registerSHi c) (registerSLo c) (registerPHi c) (registerPLo c)

setRegisterYHi : Bits 8 -> Cpu -> Cpu
setRegisterYHi d c = MkCpu (cpuMode c) (registerA c) (registerB c) (registerXHi c) (registerXLo c) d (registerYLo c) (registerDHi c) (registerDLo c) (registerSHi c) (registerSLo c) (registerPHi c) (registerPLo c)

setRegisterYLo : Bits 8 -> Cpu -> Cpu
setRegisterYLo d c = MkCpu (cpuMode c) (registerA c) (registerB c) (registerXHi c) (registerXLo c) (registerYHi c) d (registerDHi c) (registerDLo c) (registerSHi c) (registerSLo c) (registerPHi c) (registerPLo c)

registerC : Cpu -> Bits 16
--TODO implement registerC

setRegisterC : Bits16 -> Cpu -> Cpu
--TODO implement setRegisterC

registerX : Cpu -> Bits 16
--TODO implement registerX

setRegisterX : Bits 16 -> Cpu -> Cpu
--TODO implement setRegisterX

registerY : Cpu -> Bits 16
--TODO implement registerY

setRegisterY : Bits16 -> Cpu -> Cpu
--TODO implement setRegisterY


tmp1 : Bits 4
tmp1 = (intToBits 2)

tmp2 : String
tmp2 = (bitsToStr tmp1)

-- TODO come up with a way to model address space.
record AddressSpace where
       constructor MkAddressSpace
       foo : Bits 8


interface Assemblable a (n : Nat) where
          assemble : a -> Bits n

record Instruction (length : Nat) where
       constructor MkInstruction
       opcode             : Bits 8
       parameter          : Bits (8*length)
       cpuAction          : Cpu -> Cpu
       addressSpaceAction : AddressSpace -> AddressSpace




-- | a is invariant on property c of b
InvarianceProof : Type -> Type -> Type -> Type
InvarianceProof a b c = (t1 : a) -> (t2 : b) -> (act : (a -> b -> b)) -> (prp : (b -> c)) -> (prp (act t1 t2) = (prp t2))

-- | an instruction of length n is invariant on property t of a cpu
InstructionInvariantOnCpuProperty : Nat -> Type -> Type
InstructionInvariantOnCpuProperty n t = InvarianceProof (Instruction n) Cpu t

-- | NOTE this is not how inc should be implemented I'm just testing theorem proving.
--inc : Instruction 0
--inc = MkInstruction 0 0 (\cpu -> )



-- Assemblable Instruction (length : Nat) where
--            assemble instr = (opcode instr)
 
