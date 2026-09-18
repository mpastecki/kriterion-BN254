import Construction.Simulator.WireSegments

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A table word uses its fixed offset in the offline source. -/
def wireStored (offset : Nat) : WireSegment := .stored (BitVec.ofNat 256 offset)

/-- A digit table emits its 254 stored ciphertext words. -/
def wireDigit (base : Nat) : List WireSegment := (List.range 254).map fun index => wireStored (base + index)

/-- A present coefficient emits its stored value, with no per-field tag. -/
def wireCoefficient (base : Nat) (index : Nat) : List WireSegment :=
  [wireStored (base + index)]

/-- A present digit table emits its ciphertext words, with no per-field tag. -/
def wireOptionalDigit (base : Nat) (index : Nat) : List WireSegment :=
  wireDigit (base + 254 * index)

/-- The curve table emits its three coefficients before its five digit tables. -/
def publicCurveWire : List WireSegment :=
  [wireStored 917467, wireStored 917468, wireStored 917469] ++
    wireDigit 916197 ++ wireDigit 916451 ++ wireDigit 916705 ++ wireDigit 916959 ++ wireDigit 917213

/-- Each X row starts with the schema-1 header, then its five present coefficients (in the
encoding's order: c0,c1,c2,c3,c5), then its four present digit tables (x9,y6,y8,y10). -/
def publicXWire (row : Nat) : List WireSegment :=
  let base := 1017 + 9920 * row
  .tag 1 :: ([0, 1, 2, 3, 4].flatMap (wireCoefficient (base + 9915)) ++
    [3, 0, 1, 2].flatMap (wireOptionalDigit (base + 8899)))

/-- Each Y row starts with the schema-2 header, then its four present coefficients (in the
encoding's order: c0,c1,c4,c5), then its four present digit tables (x7,x9,y8,y10). -/
def publicYWire (row : Nat) : List WireSegment :=
  let base := 1017 + 9920 * row
  .tag 2 :: ([0, 1, 2, 3].flatMap (wireCoefficient (base + 6863)) ++
    [2, 3, 0, 1].flatMap (wireOptionalDigit (base + 5847)))

/-- Each Z row starts with the schema-3 header, then its five present coefficients (in the
encoding's order: c0,c2,c3,c4,c5), then its five present digit tables (x7,x9,y6,y8,y10). -/
def publicZWire (row : Nat) : List WireSegment :=
  let base := 1017 + 9920 * row
  .tag 3 :: ([0, 1, 2, 3, 4].flatMap (wireCoefficient (base + 3810)) ++
    [3, 4, 0, 1, 2].flatMap (wireOptionalDigit (base + 2540)))

/-- The public wire emits the curve, all X rows, all Y rows, and all Z rows. -/
def publicWire : List WireSegment :=
  publicCurveWire ++ (List.range 92).flatMap publicXWire ++
    (List.range 92).flatMap publicYWire ++ (List.range 92).flatMap publicZWire

end Kriterion.ArgoMAC.ArithmeticSimulator
