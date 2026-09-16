import Construction.TruncatedBitAdaptor
import Construction.ArgoMAC.CurveMembership
import Construction.ArgoMAC.Pipeline

namespace Kriterion.ArgoMAC.TruncatedCurveMembership

open BN254 Cryptography

structure Table where
  c0 : BaseField
  c1 : BaseField
  c2 : BaseField
  x3 : Vector TruncatedBitAdaptor.Table coordinateBitCount
  x5 : Vector TruncatedBitAdaptor.Table coordinateBitCount
  x7 : Vector TruncatedBitAdaptor.Table coordinateBitCount
  y4 : Vector TruncatedBitAdaptor.Table coordinateBitCount
  y6 : Vector TruncatedBitAdaptor.Table coordinateBitCount

def projectRow (rows : Vector BitAdaptor.Table coordinateBitCount) :
    Vector TruncatedBitAdaptor.Table coordinateBitCount :=
  Vector.ofFn fun index => ⟨TruncatedBitAdaptor.truncate (rows.get index).trueRow⟩

def project (table : CurveMembership.Table) : Table := {
  c0 := table.c0, c1 := table.c1, c2 := table.c2,
  x3 := projectRow table.x3, x5 := projectRow table.x5, x7 := projectRow table.x7,
  y4 := projectRow table.y4, y6 := projectRow table.y6
}

def evaluateDigit (permutations : Nat → BitAdaptor.FixedKeyPermutations)
    (table : Vector TruncatedBitAdaptor.Table coordinateBitCount) (value : BaseField)
    (inputMac : CoordinateMac) : BaseField :=
  DigitAdaptor.fromBits fun index =>
    TruncatedBitAdaptor.evaluate (permutations index.val) (table.get index)
      (coordinateValues value index) (inputMac.get index)

def curvePermutations (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (kind : Pipeline.CurveAdaptor) : Nat → BitAdaptor.FixedKeyPermutations :=
  fun position => Pipeline.fixedKeyPermutations oracle (.curve kind) position

def evaluate (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) (table : Table)
    (input : AffineInput) (inputMac : InputMac) : BaseField :=
  let c3 := evaluateDigit (curvePermutations oracle .x3) table.x3 input.x inputMac.x
  let c4 := evaluateDigit (curvePermutations oracle .y4) table.y4 input.y inputMac.y
  let c5 := evaluateDigit (curvePermutations oracle .x5) table.x5 input.x inputMac.x
  let c6 := evaluateDigit (curvePermutations oracle .y6) table.y6 input.y inputMac.y
  let c7 := evaluateDigit (curvePermutations oracle .x7) table.x7 input.x inputMac.x
  table.c0 + table.c1 * input.x ^ 3 + table.c2 * input.y ^ 2 +
    c3 * input.x ^ 2 + c4 * input.y + c5 * input.x + c6 + c7

end Kriterion.ArgoMAC.TruncatedCurveMembership
