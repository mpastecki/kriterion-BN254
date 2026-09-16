import Construction.DirectDisclosure
import Encoding

namespace Kriterion.DirectDisclosure.Wire
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



def encoding : Encoding Public := curve

@[simp] private theorem field_length (value : BaseField) :
    (field.encode value).length = 32 := by simp [field, Encoding.map]
@[simp] private theorem adaptor_length (value : BitAdaptor.Table) :
    (adaptor.encode value).length = 32 := by simp [adaptor, Encoding.map]
@[simp] private theorem digit_length (value : Vector BitAdaptor.Table coordinateBitCount) :
    (digit.encode value).length = 8128 :=
  Encoding.vector_length adaptor 32 coordinateBitCount value (fun _ => adaptor_length _)

theorem encoding_length (value : Public) : (encoding.encode value).length = 40736 := by
  simp [encoding, curve, Encoding.map, Encoding.pair]

end Kriterion.DirectDisclosure.Wire
