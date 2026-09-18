import Construction.TruncatedBitAdaptor
import Construction.ArgoMAC.Biquadratic
import Construction.ArgoMAC.Pipeline

namespace Kriterion.ArgoMAC.TruncatedBiquadratic

open BN254 Cryptography

structure Oracles where
  y6 : Nat → BitAdaptor.FixedKeyPermutations
  y8 : Nat → BitAdaptor.FixedKeyPermutations
  y10 : Nat → BitAdaptor.FixedKeyPermutations
  x7 : Nat → BitAdaptor.FixedKeyPermutations
  x9 : Nat → BitAdaptor.FixedKeyPermutations

structure Table where
  c0 : Option BaseField
  c1 : Option BaseField
  c2 : Option BaseField
  c3 : Option BaseField
  c4 : Option BaseField
  c5 : Option BaseField
  x7 : Option (Vector TruncatedBitAdaptor.Table coordinateBitCount)
  x9 : Option (Vector TruncatedBitAdaptor.Table coordinateBitCount)
  y6 : Option (Vector TruncatedBitAdaptor.Table coordinateBitCount)
  y8 : Option (Vector TruncatedBitAdaptor.Table coordinateBitCount)
  y10 : Option (Vector TruncatedBitAdaptor.Table coordinateBitCount)

def projectRows (rows : Vector BitAdaptor.Table coordinateBitCount) :
  Vector TruncatedBitAdaptor.Table coordinateBitCount :=
  Vector.ofFn fun index =>
    ⟨TruncatedBitAdaptor.truncate (rows.get index).trueRow⟩

def projectDigit (rows : Option (Vector BitAdaptor.Table coordinateBitCount)) :
    Option (Vector TruncatedBitAdaptor.Table coordinateBitCount) :=
  rows.map projectRows

def project (table : Biquadratic.Table) : Table := {
  c0 := table.c0, c1 := table.c1, c2 := table.c2, c3 := table.c3, c4 := table.c4, c5 := table.c5,
  x7 := projectDigit table.x7, x9 := projectDigit table.x9, y6 := projectDigit table.y6,
  y8 := projectDigit table.y8, y10 := projectDigit table.y10
}

def evaluateDigit (permutations : Nat → BitAdaptor.FixedKeyPermutations)
    (table : Option (Vector TruncatedBitAdaptor.Table coordinateBitCount))
    (value : BaseField) (inputMac : CoordinateMac) : BaseField :=
  match table with
  | none => 0
  | some rows => DigitAdaptor.fromBits fun index =>
      TruncatedBitAdaptor.evaluate (permutations index.val) (rows.get index)
        (coordinateValues value index) (inputMac.get index)

def coefficient (value : Option BaseField) : BaseField := value.getD 0

def evaluate (oracles : Oracles) (table : Table) (input : AffineInput)
    (inputMac : InputMac) : BaseField :=
  let c6 := evaluateDigit oracles.y6 table.y6 input.y inputMac.y
  let c7 := evaluateDigit oracles.x7 table.x7 input.x inputMac.x
  let c8 := evaluateDigit oracles.y8 table.y8 input.y inputMac.y
  let c9 := evaluateDigit oracles.x9 table.x9 input.x inputMac.x
  let c10 := evaluateDigit oracles.y10 table.y10 input.y inputMac.y
  coefficient table.c0 + coefficient table.c1 * input.x +
    coefficient table.c2 * input.y + coefficient table.c3 * input.x * input.y +
    coefficient table.c4 * input.x ^ 2 + coefficient table.c5 * input.y ^ 2 +
    c6 * input.x + c7 * input.x + c8 * input.y + c9 + c10

def evaluateY (oracles : Oracles) (table : Table) (input : AffineInput)
    (inputMac : InputMac) : BaseField :=
  coefficient table.c0 + coefficient table.c1 * input.x +
    coefficient table.c4 * input.x ^ 2 + coefficient table.c5 * input.x ^ 3 +
    evaluateDigit oracles.y8 table.y8 input.x inputMac.x * input.x ^ 2 +
    evaluateDigit oracles.x7 table.x7 input.x inputMac.x * input.x +
    evaluateDigit oracles.x9 table.x9 input.x inputMac.x

def pointOracles (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (output : Fin FieldMacToECMac.outputMacCount) (coordinate : Pipeline.PointCoordinate) : Oracles := {
  y6 := fun position => Pipeline.fixedKeyPermutations oracle (.point output coordinate .y6) position
  y8 := fun position => Pipeline.fixedKeyPermutations oracle (.point output coordinate .y8) position
  y10 := fun position => Pipeline.fixedKeyPermutations oracle (.point output coordinate .y10) position
  x7 := fun position => Pipeline.fixedKeyPermutations oracle (.point output coordinate .x7) position
  x9 := fun position => Pipeline.fixedKeyPermutations oracle (.point output coordinate .x9) position
}

end Kriterion.ArgoMAC.TruncatedBiquadratic
