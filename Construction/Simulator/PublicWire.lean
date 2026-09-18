import Construction.Simulator.WireSegments

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A table word uses its fixed offset in the offline source. -/
def wireStored (offset : Nat) : WireSegment := .stored (BitVec.ofNat 256 offset)

/-- A digit table emits its 254 stored ciphertext words. -/
def wireDigit (base : Nat) : List WireSegment := (List.range 254).map fun index => wireStored (base + index)

/-- An optional coefficient emits its tag before its value. -/
def wireCoefficient (base : Nat) : Option Nat → List WireSegment
  | none => [.tag 0]
  | some index => [.tag 1, wireStored (base + index)]

/-- An optional digit table emits its tag before its ciphertext words. -/
def wireOptionalDigit (base : Nat) : Option Nat → List WireSegment
  | none => [.tag 0]
  | some index => .tag 1 :: wireDigit (base + 254 * index)

/-- The curve table emits its three coefficients before its five digit tables. -/
def publicCurveWire : List WireSegment :=
  [wireStored 917467, wireStored 917468, wireStored 917469] ++
    wireDigit 916197 ++ wireDigit 916451 ++ wireDigit 916705 ++ wireDigit 916959 ++ wireDigit 917213

/-- Each X row follows the public encoding's coefficient and table order. -/
def publicXWire (row : Nat) : List WireSegment :=
  let base := 1017 + 9920 * row
  [some 0, some 1, some 2, some 3, none, some 4].flatMap (wireCoefficient (base + 9915)) ++
    [none, some 3, some 0, some 1, some 2].flatMap (wireOptionalDigit (base + 8899))

/-- Each Y row follows the public encoding's coefficient and table order. -/
def publicYWire (row : Nat) : List WireSegment :=
  let base := 1017 + 9920 * row
  [some 0, some 1, none, none, some 2, some 3].flatMap (wireCoefficient (base + 6863)) ++
    [some 2, some 3, none, some 0, some 1].flatMap (wireOptionalDigit (base + 5847))

/-- Each Z row follows the public encoding's coefficient and table order. -/
def publicZWire (row : Nat) : List WireSegment :=
  let base := 1017 + 9920 * row
  [some 0, none, some 1, some 2, some 3, some 4].flatMap (wireCoefficient (base + 3810)) ++
    [some 3, some 4, some 0, some 1, some 2].flatMap (wireOptionalDigit (base + 2540))

/-- The public wire emits the curve, all X rows, all Y rows, and all Z rows. -/
def publicWire : List WireSegment :=
  publicCurveWire ++ (List.range 92).flatMap publicXWire ++
    (List.range 92).flatMap publicYWire ++ (List.range 92).flatMap publicZWire

end Kriterion.ArgoMAC.ArithmeticSimulator
