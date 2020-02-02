import Data.Bits
import Data.Vect

abelianLength : Bits (n + m) -> Bits (m + n)
abelianLength bs = nbs
              where
              bsInt : Integer
              bsInt = bitsToInt bs
              nbs   : Bits (m + n)
              nbs   = intToBits bsInt

concatBits : (n : Nat) -> (m : Nat ) -> Bits n -> Bits m -> Bits (n + m)
concatBits n m bh bl = or bhnew blnew
           where
           blnew : Bits (n + m)
           blnew = abelianLength $ zeroExtend bl
           shift : Bits (n + m)
           shift = abelianLength $ MkBits $ natToBits m
           bhext : Bits (n + m)
           bhext = zeroExtend bh
           bhnew : Bits (n + m)
           bhnew = shiftLeft bhext shift

-- TODO finish formulating cpu details
data FlagState = Set | Reset
record CpuStatus where
       constructor MkCpuStatus
       carryFlag      : FlagState
       zeroFlag       : FlagState
       interruptFlag  : FlagState
       decimalFlag    : FlagState
       indexBreakFlag : FlagState
       accumMemFlag   : FlagState
       overFlowFlag   : FlagState
       negativeFlag   : FlagState
       emulationFlag  : FlagState

record Cpu where
       constructor MkCpu
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
defaultCpu = MkCpu (intToBits 0) (intToBits 0) (intToBits 0) (intToBits 0) (intToBits 0) (intToBits 0) (intToBits 0) (intToBits 0) (intToBits 0) (intToBits 0) (intToBits 0) (intToBits 0)

setRegisterA : Bits 8 -> Cpu -> Cpu
setRegisterA d c = MkCpu d (registerB c) (registerXHi c) (registerXLo c) (registerYHi c) (registerYLo c) (registerDHi c) (registerDLo c) (registerSHi c) (registerSLo c) (registerPHi c) (registerPLo c)

setRegisterB : Bits 8 -> Cpu -> Cpu
setRegisterB d c = MkCpu (registerA c) d (registerXHi c) (registerXLo c) (registerYHi c) (registerYLo c) (registerDHi c) (registerDLo c) (registerSHi c) (registerSLo c) (registerPHi c) (registerPLo c)

setRegisterXHi : Bits 8 -> Cpu -> Cpu
setRegisterXHi d c = MkCpu (registerA c) (registerB c) d (registerXLo c) (registerYHi c) (registerYLo c) (registerDHi c) (registerDLo c) (registerSHi c) (registerSLo c) (registerPHi c) (registerPLo c)

setRegisterXLo : Bits 8 -> Cpu -> Cpu
setRegisterXLo d c = MkCpu (registerA c) (registerB c) (registerXHi c) d (registerYHi c) (registerYLo c) (registerDHi c) (registerDLo c) (registerSHi c) (registerSLo c) (registerPHi c) (registerPLo c)

setRegisterYHi : Bits 8 -> Cpu -> Cpu
setRegisterYHi d c = MkCpu (registerA c) (registerB c) (registerXHi c) (registerXLo c) d (registerYLo c) (registerDHi c) (registerDLo c) (registerSHi c) (registerSLo c) (registerPHi c) (registerPLo c)

setRegisterYLo : Bits 8 -> Cpu -> Cpu
setRegisterYLo d c = MkCpu (registerA c) (registerB c) (registerXHi c) (registerXLo c) (registerYHi c) d (registerDHi c) (registerDLo c) (registerSHi c) (registerSLo c) (registerPHi c) (registerPLo c)

registerC : Cpu -> Bits 16
registerC cpu = concatBits 8 8 (registerA cpu) (registerB cpu)

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

data AddressModifier = NoneModifiedAddress | CpuModifiedAddress | PpuModifiedAddress

-- NOTE I'm not sure how well I like the design I'm currently going with, but we will see how it works out.
data AddressSpace : Type where
     EmptySpace      : AddressSpace
     SetAddressValue : AddressModifier -> Bits 24 -> Bits 8 -> AddressSpace -> AddressSpace

shedAddressSpaceLayer : AddressSpace -> (AddressModifier, Bits 24, Bits 8, AddressSpace)
shedAddressSpaceLayer EmptySpace = (NoneModifiedAddress, intToBits 0, intToBits 0, EmptySpace)
shedAddressSpaceLayer (SetAddressValue am ad d as) = (am, ad, d, as)

getAddressHistory : Bits 24 -> AddressSpace -> List (Bits 8, AddressModifier)
getAddressHistory bs EmptySpace = []
getAddressHistory bs adr = hstr ++ getAddressHistory bs adrn
             where
              adrs : Bits 24
              adrs = fst (snd (shedAddressSpaceLayer adr))
              dta  : Bits 8
              dta  = fst (snd (snd (shedAddressSpaceLayer adr)))
              mod  : AddressModifier
              mod  = fst (shedAddressSpaceLayer adr)
              adrn : AddressSpace
              adrn = snd (snd (snd (shedAddressSpaceLayer adr)))
              hstr : List (Bits 8, AddressModifier)
              hstr = if adrs == bs then [(dta, mod)] else []

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
 
