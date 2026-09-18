import Construction.Simulator.WordOutput

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A fixed wire segment selects one tag byte or one stored 256-bit word. -/
inductive WireSegment
  | tag (value : Fin 256)
  | stored (offset : Word)

/-- The segment loads its value and emits its fixed number of bits.
Register eleven supplies the first address of the source data. -/
def WireSegment.program : WireSegment → List LinearInstruction
  | .tag value => [.constant 8 (BitVec.ofNat 256 value.val)] ++ wordOutput 8
  | .stored offset =>
      [.constant 9 offset, .arithmetic .add 9 11 9, .load 8 9] ++ wordOutput 256

/-- The emitter processes segments in reverse order because each output bit is prepended. -/
def wireSegmentsProgram (segments : List WireSegment) : List LinearInstruction :=
  segments.reverse.flatMap WireSegment.program

end Kriterion.ArgoMAC.ArithmeticSimulator
