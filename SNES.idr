import Data.Bits
import Data.Vect

-- TODO finish formulating cpu details
record Cpu where
       constructor MkCpu
       registerA   : Bits 8
       registerB   : Bits 8
       registerXHi : Bits 8
       registerXLo : Bits 8
       registerYHi : Bits 8
       registerYLo : Bits 8

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


InvarianceProof : Type -> Type -> Type -> Type
InvarianceProof a b c = (t1 : a) -> (t2 : b) -> (act : (a -> b -> b)) -> (prp : (b -> c)) -> (prp (act t1 t2) = (prp t2))

-- TODO figure out how to assemble instructions into binary
-- Assemblable Instruction (length : Nat) where
--            assemble instr = (opcode instr)
 
