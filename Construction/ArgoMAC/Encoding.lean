import Construction.Garbling
import Encoding

namespace Kriterion.ArgoMAC

open BN254

namespace Wire

def field : Encoding BaseField :=
  (Encoding.natural 32).map
    (fun value => ⟨value.val, lt_trans value.val_lt (by decide)⟩)
    (fun value => value.val)
    (fun value => ZMod.natCast_zmod_val value)

def adaptor : Encoding BitAdaptor.Table :=
  (Encoding.natural 32).map
    (fun value => ⟨value.trueRow.toNat, value.trueRow.isLt⟩)
    (fun value => ⟨BitVec.ofNat 256 value.val⟩)
    (fun value => by cases value; simp)

def digit := adaptor.vector coordinateBitCount

def curve : Encoding CurveMembership.Table :=
  (field.pair (field.pair (field.pair
    (digit.pair (digit.pair (digit.pair (digit.pair digit))))))).map
    (fun value => (value.c0, value.c1, value.c2,
      value.x3, value.x5, value.x7, value.y4, value.y6))
    (fun ⟨c0, c1, c2, x3, x5, x7, y4, y6⟩ => ⟨c0, c1, c2, x3, x5, x7, y4, y6⟩)
    (fun _ => rfl)

def biquadratic : Encoding Biquadratic.Table :=
  let coefficient := field.option
  let rows := digit.option
  (coefficient.pair (coefficient.pair (coefficient.pair (coefficient.pair
    (coefficient.pair (coefficient.pair
      (rows.pair (rows.pair (rows.pair (rows.pair rows)))))))))).map
    (fun value => (value.c0, value.c1, value.c2, value.c3, value.c4, value.c5,
      value.x7, value.x9, value.y6, value.y8, value.y10))
    (fun ⟨c0, c1, c2, c3, c4, c5, x7, x9, y6, y8, y10⟩ =>
      ⟨c0, c1, c2, c3, c4, c5, x7, x9, y6, y8, y10⟩)
    (fun _ => rfl)

def pointMAC : Encoding FieldMacToECMac.Table :=
  let rows := biquadratic.vector FieldMacToECMac.outputMacCount
  (rows.pair (rows.pair rows)).map
    (fun value => (value.x, value.y, value.z))
    (fun ⟨x, y, z⟩ => ⟨x, y, z⟩)
    (fun _ => rfl)

/-- This encoding includes every public field and each optional-field tag. -/
def encoding : Encoding Pipeline.Table :=
  (curve.pair pointMAC).map
    (fun value => (value.curve, value.pointMAC))
    (fun ⟨curve, pointMAC⟩ => ⟨curve, pointMAC⟩)
    (fun _ => rfl)

@[simp] private theorem field_length (value : BaseField) :
    (field.encode value).length = 32 := by simp [field, Encoding.map]

@[simp] private theorem adaptor_length (value : BitAdaptor.Table) :
    (adaptor.encode value).length = 32 := by simp [adaptor, Encoding.map]

@[simp] private theorem digit_length (value : Vector BitAdaptor.Table coordinateBitCount) :
    (digit.encode value).length = 8128 :=
  Encoding.vector_length adaptor 32 coordinateBitCount value (fun _ => adaptor_length _)

@[simp] theorem curve_length (value : CurveMembership.Table) :
    (curve.encode value).length = 40736 := by
  simp [curve, Encoding.map, Encoding.pair]

@[simp] private theorem coefficient_length (value : Option BaseField) :
    (field.option.encode value).length = if value.isSome then 33 else 1 := by
  cases value <;> simp [Encoding.option]

@[simp] private theorem rows_length (value : Option (Vector BitAdaptor.Table coordinateBitCount)) :
    (digit.option.encode value).length = if value.isSome then 8129 else 1 := by
  cases value <;> simp [Encoding.option]

theorem biquadratic_length (value : Biquadratic.Table) :
    (biquadratic.encode value).length =
      (if value.c0.isSome then 33 else 1) + ((if value.c1.isSome then 33 else 1) +
      ((if value.c2.isSome then 33 else 1) + ((if value.c3.isSome then 33 else 1) +
      ((if value.c4.isSome then 33 else 1) + ((if value.c5.isSome then 33 else 1) +
      ((if value.x7.isSome then 8129 else 1) + ((if value.x9.isSome then 8129 else 1) +
      ((if value.y6.isSome then 8129 else 1) + ((if value.y8.isSome then 8129 else 1) +
      (if value.y10.isSome then 8129 else 1)))))))))) := by
  simp [biquadratic, Encoding.map, Encoding.pair]

@[simp] private theorem x_length (c0 c1 c2 c3 c5 : BaseField)
    (randomness : Biquadratic.XRandomness) (oracles : Biquadratic.Oracles) (key : InputMacKey) :
    (biquadratic.encode (Biquadratic.garbleX c0 c1 c2 c3 c5 randomness oracles key)).length = 32683 := by
  rw [biquadratic_length]
  simp [Biquadratic.garbleX]

@[simp] private theorem y_length (c0 c1 c4 c5 : BaseField)
    (randomness : Biquadratic.YRandomness) (oracles : Biquadratic.Oracles) (key : InputMacKey) :
    (biquadratic.encode (Biquadratic.garbleY c0 c1 c4 c5 randomness oracles key)).length = 32651 := by
  rw [biquadratic_length]
  simp [Biquadratic.garbleY]

@[simp] private theorem z_length (c0 c2 c3 c4 c5 : BaseField)
    (randomness : Biquadratic.ZRandomness) (oracles : Biquadratic.Oracles) (key : InputMacKey) :
    (biquadratic.encode (Biquadratic.garbleZ c0 c2 c3 c4 c5 randomness oracles key)).length = 40811 := by
  rw [biquadratic_length]
  simp [Biquadratic.garbleZ]

private theorem pointMAC_length (rows : FieldMacToECMac.Rows)
    (randomness : FieldMacToECMac.Randomness) (oracles : FieldMacToECMac.Oracles) (key : InputMacKey) :
    (pointMAC.encode (FieldMacToECMac.garble rows randomness oracles key)).length = 9765340 := by
  simp only [pointMAC, Encoding.map, Encoding.pair, List.length_append]
  rw [Encoding.vector_length biquadratic 32683 _ _ (by
        intro index; simp [FieldMacToECMac.garble, FieldMacToECMac.garbleRow]),
      Encoding.vector_length biquadratic 32651 _ _ (by
        intro index; simp [FieldMacToECMac.garble, FieldMacToECMac.garbleRow]),
      Encoding.vector_length biquadratic 40811 _ _ (by
        intro index; simp [FieldMacToECMac.garble, FieldMacToECMac.garbleRow])]
  rfl

/-- Every scalar and random tape produces the same complete ciphertext length. -/
theorem garble_length (construction : Construction) (scalar : NonZeroScalar)
    (randomness : Garbling.Randomness) :
    (encoding.encode (Garbling.garble construction scalar randomness).1).length = 9806076 := by
  simp [encoding, Encoding.map, Encoding.pair, Garbling.garble, Pipeline.garble, pointMAC_length]

end Wire
end Kriterion.ArgoMAC
