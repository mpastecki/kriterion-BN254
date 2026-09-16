import Construction.ConditionalDisclosure
import Encoding

namespace Kriterion.ConditionalDisclosure.Wire

open BN254 ArgoMAC

private def field : Encoding BaseField :=
  (Encoding.natural 32).map
    (fun value => ⟨value.val, lt_trans value.val_lt (by decide)⟩)
    (fun value => value.val)
    (fun value => ZMod.natCast_zmod_val value)

private def adaptor : Encoding BitAdaptor.Table :=
  (Encoding.natural 32).map
    (fun value => ⟨value.trueRow.toNat, value.trueRow.isLt⟩)
    (fun value => ⟨BitVec.ofNat 256 value.val⟩)
    (fun value => by cases value; simp)

private def digit := adaptor.vector coordinateBitCount

private def curve : Encoding CurveMembership.Table :=
  (field.pair (field.pair (field.pair
    (digit.pair (digit.pair (digit.pair (digit.pair digit))))))).map
    (fun value => (value.c0, value.c1, value.c2,
      value.x3, value.x5, value.x7, value.y4, value.y6))
    (fun ⟨c0, c1, c2, x3, x5, x7, y4, y6⟩ => ⟨c0, c1, c2, x3, x5, x7, y4, y6⟩)
    (fun _ => rfl)


private def ciphertext : Encoding Ciphertext :=
  (Encoding.natural 32).map
    (fun value => ⟨value.toNat, value.isLt⟩)
    (fun value => BitVec.ofNat 256 value.val)
    (fun value => by simp)

def encoding : Encoding Public :=
  (curve.pair ciphertext).map
    (fun value => (value.curve, value.scalarCiphertext))
    (fun value => ⟨value.1, value.2⟩)
    (fun _ => rfl)

@[simp] private theorem field_length (value : BaseField) :
    (field.encode value).length = 32 := by simp [field, Encoding.map]

@[simp] private theorem adaptor_length (value : BitAdaptor.Table) :
    (adaptor.encode value).length = 32 := by simp [adaptor, Encoding.map]

@[simp] private theorem digit_length (value : Vector BitAdaptor.Table coordinateBitCount) :
    (digit.encode value).length = 8128 :=
  Encoding.vector_length adaptor 32 coordinateBitCount value (fun _ => adaptor_length _)

@[simp] private theorem curve_length (value : CurveMembership.Table) :
    (curve.encode value).length = 40736 := by
  simp [curve, Encoding.map, Encoding.pair]

@[simp] private theorem ciphertext_length (value : Ciphertext) :
    (ciphertext.encode value).length = 32 := by simp [ciphertext, Encoding.map]

theorem encoding_length (value : Public) :
    (encoding.encode value).length = 40768 := by
  simp [encoding, Encoding.map, Encoding.pair]

end Kriterion.ConditionalDisclosure.Wire
