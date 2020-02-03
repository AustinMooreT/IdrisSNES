import Data.Bits
import Data.Vect

-- | BEGIN Bits Utilities
   -- utilities not provided by Data.Bits

commuteLength : {n : Nat} -> {m : Nat} -> Bits (n + m) -> Bits (m + n)
commuteLength {n} {m} bs = replace commuteProof bs
              where
              commuteProof : n + m = m + n
              commuteProof = plusCommutative n m

concatBits : {n : Nat} -> {m : Nat} -> Bits n -> Bits m -> Bits (n + m)
concatBits {n} {m} bh bl = or bhnew blnew
           where
           blnew : Bits (n + m)
           blnew = commuteLength $ zeroExtend bl
           shift : Bits (n + m)
           shift = commuteLength $ MkBits $ natToBits m
           bhext : Bits (n + m)
           bhext = zeroExtend bh
           bhnew : Bits (n + m)
           bhnew = shiftLeft bhext shift

-- TODO clean this up.
getLowByte : Bits 16 -> Bits 8
getLowByte bs = nnbs 8
           where
           bsInt  : Integer
           bsInt  = bitsToInt bs
           nbs    : (m : Nat) -> Bits (m + 8)
           nbs m  = intToBits bsInt
           nnbs   : Nat -> Bits 8
           nnbs m = truncate (nbs m)

getHighByte : Bits 16 -> Bits 8
getHighByte bs = getLowByte $ shiftRightLogical bs (intToBits 8)

-- | END Bits Utilities

-- TODO finish formulating cpu details
record CpuStatus where
       constructor MkCpuStatus
       carryFlag      : Bits 1
       zeroFlag       : Bits 1
       interruptFlag  : Bits 1
       decimalFlag    : Bits 1
       indexBreakFlag : Bits 1
       accumMemFlag   : Bits 1
       overFlowFlag   : Bits 1
       negativeFlag   : Bits 1
       emulationFlag  : Bits 1

zBits : (n : Nat) -> Bits n
zBits n = intToBits 0

zBits1 : Bits 1
zBits1 = zBits 1

zBits8 : Bits 8
zBits8 = zBits 8

zStatus : CpuStatus
zStatus = MkCpuStatus zBits1 zBits1 zBits1 zBits1 zBits1 zBits1 zBits1 zBits1 zBits1

cpuStatusToByte : CpuStatus -> Bits 8
cpuStatusToByte cpus = concatBits (negativeFlag   cpus) (
                       concatBits (overFlowFlag   cpus) (
                       concatBits (accumMemFlag   cpus) (
                       concatBits (indexBreakFlag cpus) (
                       concatBits (decimalFlag    cpus) (
                       concatBits (interruptFlag  cpus) (
                       concatBits (zeroFlag       cpus) (
                       carryFlag cpus)))))))


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

zCpu : Cpu
zCpu = MkCpu zBits8 zBits8 zBits8 zBits8 zBits8 zBits8 zBits8 zBits8 zBits8 zBits8 zBits8 zBits8

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
registerC cpu = concatBits (registerA cpu) (registerB cpu)

setRegisterC : Bits 16 -> Cpu -> Cpu
setRegisterC bs cpu = setRegisterA (getHighByte bs) $ setRegisterB (getLowByte bs) cpu

registerX : Cpu -> Bits 16
registerX cpu = concatBits (registerXHi cpu) (registerXLo cpu)

setRegisterX : Bits 16 -> Cpu -> Cpu
setRegisterX bs cpu = setRegisterXHi (getHighByte bs) $ setRegisterXLo (getLowByte bs) cpu

registerY : Cpu -> Bits 16
registerY cpu = concatBits (registerYHi cpu) (registerYLo cpu)

setRegisterY : Bits 16 -> Cpu -> Cpu
setRegisterY bs cpu = setRegisterYHi (getHighByte bs) $ setRegisterYLo (getLowByte bs) cpu

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

record Instruction (length : Nat) where
       constructor MkInstruction
       opcode             : Bits 8
       parameter          : Bits (8*length)
       cpuAction          : Cpu -> Cpu
       addressSpaceAction : AddressSpace -> AddressSpace

