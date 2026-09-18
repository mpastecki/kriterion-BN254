import Construction.ArgoMAC.CurveMembership
import Construction.ArgoMAC.Coordinates

namespace Kriterion.ArgoMAC.Cubic

open BN254

/-- The four coefficients of a polynomial in the x coordinate. -/
structure Coefficients where
  c0 : BaseField
  c1 : BaseField
  c2 : BaseField
  c3 : BaseField

def polynomial (coefficients : Coefficients) (x : BaseField) : BaseField :=
  coefficients.c0 + coefficients.c1 * x + coefficients.c2 * x ^ 2 + coefficients.c3 * x ^ 3

/-- This polynomial represents the sparse RCB Y row on the curve. -/
def fromY (row : Coordinates.Coefficients) : Coefficients :=
  ⟨row.constant + 3 * row.ySquared, row.x, row.xSquared, row.ySquared⟩

structure Randomness where
  r1 : BaseField
  r2 : BaseField
  r3 : BaseField

structure Oracles where
  high : Nat → BitAdaptor.FixedKeyOracle
  middle : Nat → BitAdaptor.FixedKeyOracle
  low : Nat → BitAdaptor.FixedKeyOracle

/-- Each of the three adaptors consumes the same x label vector. -/
structure Table where
  coefficients : Coefficients
  high : Vector BitAdaptor.Table coordinateBitCount
  middle : Vector BitAdaptor.Table coordinateBitCount
  low : Vector BitAdaptor.Table coordinateBitCount

def garble (coefficients : Coefficients) (randomness : Randomness)
    (oracles : Oracles) (key : CoordinateMacKey) : Table :=
  let high := DigitAdaptor.garble oracles.high (-randomness.r3) key
  let highOffset := DigitAdaptor.bitsK high.2
  let middle := DigitAdaptor.garble oracles.middle (-(randomness.r2 + highOffset)) key
  let middleOffset := DigitAdaptor.bitsK middle.2
  let low := DigitAdaptor.garble oracles.low (-(randomness.r1 + middleOffset)) key
  let lowOffset := DigitAdaptor.bitsK low.2
  { coefficients := ⟨coefficients.c0 - lowOffset, coefficients.c1 + randomness.r1,
      coefficients.c2 + randomness.r2, coefficients.c3 + randomness.r3⟩
    high := high.1
    middle := middle.1
    low := low.1 }

def evaluate (oracles : Oracles) (table : Table) (x : BaseField)
    (labels : CoordinateMac) : BaseField :=
  polynomial table.coefficients x +
    CurveMembership.evaluateDigit oracles.high table.high x labels * x ^ 2 +
    CurveMembership.evaluateDigit oracles.middle table.middle x labels * x +
    CurveMembership.evaluateDigit oracles.low table.low x labels

end Kriterion.ArgoMAC.Cubic
