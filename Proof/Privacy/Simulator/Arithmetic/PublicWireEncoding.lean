import Construction.ArgoMAC.Encoding
import Proof.Privacy.Simulator.Arithmetic.EncodingBits
import Proof.Privacy.Simulator.Arithmetic.WireSegments

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol

/-- A public field uses one canonical 256-bit word. -/
theorem publicField_bits (value : BaseField) :
    (Wire.field.encode value).flatMap (fun byte => bits 8 byte.val) = bits 256 value.val := by
  exact naturalEncoding_bits 32 ⟨value.val, lt_trans value.val_lt (by decide)⟩

/-- A public ciphertext row uses all bits of its stored word. -/
theorem publicAdaptor_bits (value : BitAdaptor.Table) :
    (Wire.adaptor.encode value).flatMap (fun byte => bits 8 byte.val) = bits 256 value.trueRow.toNat := by
  exact naturalEncoding_bits 32 ⟨value.trueRow.toNat, value.trueRow.isLt⟩

/-- A digit emits each ciphertext word in coordinate order. -/
theorem publicDigit_bits (value : Vector BitAdaptor.Table coordinateBitCount) :
    (Wire.digit.encode value).flatMap (fun byte => bits 8 byte.val) =
      value.toList.flatMap (fun table => bits 256 table.trueRow.toNat) := by
  rw [Wire.digit, vectorEncoding_encode, List.flatMap_assoc]
  simp only [publicAdaptor_bits]

/-- An absent field emits its tag alone. -/
theorem publicOption_none {A : Type} (encoding : Encoding A) :
    (encoding.option.encode none).flatMap (fun byte => bits 8 byte.val) = bits 8 0 := by
  simp [Encoding.option]

/-- A present field emits its tag before its complete value. -/
theorem publicOption_some {A : Type} (encoding : Encoding A) (value : A) :
    (encoding.option.encode (some value)).flatMap (fun byte => bits 8 byte.val) =
      bits 8 1 ++ (encoding.encode value).flatMap (fun byte => bits 8 byte.val) := by
  simp [Encoding.option]

end Kriterion.ArgoMAC.ArithmeticSimulator
