import Construction.Simulator.PublicWire
import Proof.Privacy.Simulator.Arithmetic.PublicWireEncoding

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol

/-- A coefficient load emits exactly the public field encoding. -/
theorem wireStored_field (ram : Word → Word) (pointer : Word) (offset : Nat) (value : BaseField)
    (stored : ram (pointer + BitVec.ofNat 256 offset) = BitVec.ofNat 256 value.val) :
    (wireStored offset).wire ram pointer =
      (Wire.field.encode value).flatMap (fun byte => bits 8 byte.val) := by
  rw [publicField_bits]
  have fits : value.val < 2 ^ 256 := lt_trans value.val_lt (by decide)
  change bits 256 (ram (pointer + BitVec.ofNat 256 offset)).toNat = _
  rw [stored, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]

/-- A digit load emits exactly the public ciphertext encoding. -/
theorem wireDigit_bits (ram : Word → Word) (pointer : Word) (offset : Nat)
    (value : Vector BitAdaptor.Table coordinateBitCount)
    (stored : ∀ index : Fin coordinateBitCount,
      ram (pointer + BitVec.ofNat 256 (offset + index.val)) = (value.get index).trueRow) :
    (wireDigit offset).flatMap (WireSegment.wire ram pointer) =
      (Wire.digit.encode value).flatMap (fun byte => bits 8 byte.val) := by
  rw [publicDigit_bits]
  have words : (List.range 254).map (fun index => (ram (pointer + BitVec.ofNat 256 (offset + index))).toNat) =
      value.toList.map (fun table => table.trueRow.toNat) := by
    apply List.ext_getElem
    · simp [coordinateBitCount]
    · intro index left right
      have bound : index < coordinateBitCount := by simpa [coordinateBitCount] using left
      simp only [List.getElem_map, List.getElem_range]
      rw [stored ⟨index, bound⟩]
      rfl
  have wires := congrArg (List.flatMap (bits 256)) words
  simpa only [wireDigit, List.flatMap_map, Function.comp_def, WireSegment.wire, wireStored] using wires

/-- An optional field emits the tag and the stored coefficient. -/
theorem wireCoefficient_bits (ram : Word → Word) (pointer : Word) (base index : Nat) (value : BaseField)
    (stored : ram (pointer + BitVec.ofNat 256 (base + index)) = BitVec.ofNat 256 value.val) :
    (wireCoefficient base (some index)).flatMap (WireSegment.wire ram pointer) =
      (Wire.field.option.encode (some value)).flatMap (fun byte => bits 8 byte.val) := by
  simp only [wireCoefficient, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    publicOption_some]
  change bits 8 1 ++ (wireStored (base + index)).wire ram pointer = _
  rw [wireStored_field ram pointer (base + index) value stored]

/-- An optional digit emits the tag and the complete stored table. -/
theorem wireOptionalDigit_bits (ram : Word → Word) (pointer : Word) (base index : Nat)
    (value : Vector BitAdaptor.Table coordinateBitCount)
    (stored : ∀ bit : Fin coordinateBitCount,
      ram (pointer + BitVec.ofNat 256 (base + 254 * index + bit.val)) = (value.get bit).trueRow) :
    (wireOptionalDigit base (some index)).flatMap (WireSegment.wire ram pointer) =
      (Wire.digit.option.encode (some value)).flatMap (fun byte => bits 8 byte.val) := by
  simp only [wireOptionalDigit, List.flatMap_cons, WireSegment.wire, publicOption_some]
  rw [wireDigit_bits ram pointer (base + 254 * index) value stored]
  rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
