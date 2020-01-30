import Data.Bits
import Data.Vect

-- TODO finish formulating cpu details
record Cpu where
       constructor MkCpu
       RegisterA   : Bits 8
       RegisterB   : Bits 8
       RegisterX   : Bits 16
       RegisterY   : Bits 16
       


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



-- TODO figure out how to assemble instructions into binary
-- Assemblable Instruction (length : Nat) where
--            assemble instr = (opcode instr)

