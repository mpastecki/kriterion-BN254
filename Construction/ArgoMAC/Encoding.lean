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

/-- The old encoding: every optional field carries its own one-byte tag. Kept only as the
fallback branch of `biquadratic`, so `biquadratic`'s round trip stays total over every
`Biquadratic.Table`, not only the three shapes real garbling produces. -/
private def biquadraticFallback : Encoding Biquadratic.Table :=
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

/-- The present fields of an X-shaped row, in the encoding's order. -/
private structure XPayload where
  c0 : BaseField
  c1 : BaseField
  c2 : BaseField
  c3 : BaseField
  c5 : BaseField
  x9 : Vector BitAdaptor.Table coordinateBitCount
  y6 : Vector BitAdaptor.Table coordinateBitCount
  y8 : Vector BitAdaptor.Table coordinateBitCount
  y10 : Vector BitAdaptor.Table coordinateBitCount

/-- The present fields of a Y-shaped row, in the encoding's order. -/
private structure YPayload where
  c0 : BaseField
  c1 : BaseField
  c4 : BaseField
  c5 : BaseField
  x7 : Vector BitAdaptor.Table coordinateBitCount
  x9 : Vector BitAdaptor.Table coordinateBitCount
  y8 : Vector BitAdaptor.Table coordinateBitCount
  y10 : Vector BitAdaptor.Table coordinateBitCount

/-- The present fields of a Z-shaped row, in the encoding's order. -/
private structure ZPayload where
  c0 : BaseField
  c2 : BaseField
  c3 : BaseField
  c4 : BaseField
  c5 : BaseField
  x7 : Vector BitAdaptor.Table coordinateBitCount
  x9 : Vector BitAdaptor.Table coordinateBitCount
  y6 : Vector BitAdaptor.Table coordinateBitCount
  y8 : Vector BitAdaptor.Table coordinateBitCount
  y10 : Vector BitAdaptor.Table coordinateBitCount

private def xPayload : Encoding XPayload :=
  (field.pair (field.pair (field.pair (field.pair
    (field.pair (digit.pair (digit.pair (digit.pair digit)))))))).map
    (fun value => (value.c0, value.c1, value.c2, value.c3, value.c5,
      value.x9, value.y6, value.y8, value.y10))
    (fun ⟨c0, c1, c2, c3, c5, x9, y6, y8, y10⟩ => ⟨c0, c1, c2, c3, c5, x9, y6, y8, y10⟩)
    (fun _ => rfl)

private def yPayload : Encoding YPayload :=
  (field.pair (field.pair (field.pair (field.pair
    (digit.pair (digit.pair (digit.pair digit))))))).map
    (fun value => (value.c0, value.c1, value.c4, value.c5,
      value.x7, value.x9, value.y8, value.y10))
    (fun ⟨c0, c1, c4, c5, x7, x9, y8, y10⟩ => ⟨c0, c1, c4, c5, x7, x9, y8, y10⟩)
    (fun _ => rfl)

private def zPayload : Encoding ZPayload :=
  (field.pair (field.pair (field.pair (field.pair
    (field.pair (digit.pair (digit.pair (digit.pair (digit.pair digit))))))))).map
    (fun value => (value.c0, value.c2, value.c3, value.c4, value.c5,
      value.x7, value.x9, value.y6, value.y8, value.y10))
    (fun ⟨c0, c2, c3, c4, c5, x7, x9, y6, y8, y10⟩ =>
      ⟨c0, c2, c3, c4, c5, x7, x9, y6, y8, y10⟩)
    (fun _ => rfl)

private def tableOfX (value : XPayload) : Biquadratic.Table :=
  { c0 := some value.c0, c1 := some value.c1, c2 := some value.c2,
    c3 := some value.c3, c4 := none, c5 := some value.c5,
    x7 := none, x9 := some value.x9, y6 := some value.y6,
    y8 := some value.y8, y10 := some value.y10 }

private def tableOfY (value : YPayload) : Biquadratic.Table :=
  { c0 := some value.c0, c1 := some value.c1, c2 := none, c3 := none,
    c4 := some value.c4, c5 := some value.c5,
    x7 := some value.x7, x9 := some value.x9, y6 := none,
    y8 := some value.y8, y10 := some value.y10 }

private def tableOfZ (value : ZPayload) : Biquadratic.Table :=
  { c0 := some value.c0, c1 := none, c2 := some value.c2,
    c3 := some value.c3, c4 := some value.c4, c5 := some value.c5,
    x7 := some value.x7, x9 := some value.x9, y6 := some value.y6,
    y8 := some value.y8, y10 := some value.y10 }

/-- `some` exactly when `value` has the X shape; `none` otherwise. One flat match keeps this
a two-leaf case split, unlike matching the whole `Table` against a full field pattern. -/
private def xPayloadOf (value : Biquadratic.Table) : Option XPayload :=
  match value.c0, value.c1, value.c2, value.c3, value.c4, value.c5,
      value.x7, value.x9, value.y6, value.y8, value.y10 with
  | some c0, some c1, some c2, some c3, none, some c5,
      none, some x9, some y6, some y8, some y10 =>
      some ⟨c0, c1, c2, c3, c5, x9, y6, y8, y10⟩
  | _, _, _, _, _, _, _, _, _, _, _ => none

private def yPayloadOf (value : Biquadratic.Table) : Option YPayload :=
  match value.c0, value.c1, value.c2, value.c3, value.c4, value.c5,
      value.x7, value.x9, value.y6, value.y8, value.y10 with
  | some c0, some c1, none, none, some c4, some c5,
      some x7, some x9, none, some y8, some y10 =>
      some ⟨c0, c1, c4, c5, x7, x9, y8, y10⟩
  | _, _, _, _, _, _, _, _, _, _, _ => none

private def zPayloadOf (value : Biquadratic.Table) : Option ZPayload :=
  match value.c0, value.c1, value.c2, value.c3, value.c4, value.c5,
      value.x7, value.x9, value.y6, value.y8, value.y10 with
  | some c0, none, some c2, some c3, some c4, some c5,
      some x7, some x9, some y6, some y8, some y10 =>
      some ⟨c0, c2, c3, c4, c5, x7, x9, y6, y8, y10⟩
  | _, _, _, _, _, _, _, _, _, _, _ => none

private theorem tableOfX_payloadOf (value : Biquadratic.Table) (payload : XPayload)
    (encoded : xPayloadOf value = some payload) : tableOfX payload = value := by
  rcases value with ⟨c0, c1, c2, c3, c4, c5, x7, x9, y6, y8, y10⟩
  unfold xPayloadOf at encoded
  split at encoded
  · injection encoded with encoded
    subst payload
    simp_all [tableOfX]
  · simp_all

private theorem tableOfY_payloadOf (value : Biquadratic.Table) (payload : YPayload)
    (encoded : yPayloadOf value = some payload) : tableOfY payload = value := by
  rcases value with ⟨c0, c1, c2, c3, c4, c5, x7, x9, y6, y8, y10⟩
  unfold yPayloadOf at encoded
  split at encoded
  · injection encoded with encoded
    subst payload
    simp_all [tableOfY]
  · simp_all

private theorem tableOfZ_payloadOf (value : Biquadratic.Table) (payload : ZPayload)
    (encoded : zPayloadOf value = some payload) : tableOfZ payload = value := by
  rcases value with ⟨c0, c1, c2, c3, c4, c5, x7, x9, y6, y8, y10⟩
  unfold zPayloadOf at encoded
  split at encoded
  · injection encoded with encoded
    subst payload
    simp_all [tableOfZ]
  · simp_all

private def encodeBiquadratic (value : Biquadratic.Table) : List (Fin 256) :=
  match xPayloadOf value with
  | some payload => (1 : Fin 256) :: xPayload.encode payload
  | none => match yPayloadOf value with
    | some payload => (2 : Fin 256) :: yPayload.encode payload
    | none => match zPayloadOf value with
      | some payload => (3 : Fin 256) :: zPayload.encode payload
      | none => (0 : Fin 256) :: biquadraticFallback.encode value

private def decodeBiquadratic (bytes : List (Fin 256)) :
    Option (Biquadratic.Table × List (Fin 256)) := match bytes with
  | [] => none
  | header :: tail =>
    if header = (1 : Fin 256) then
      (xPayload.decode tail).map fun result => (tableOfX result.1, result.2)
    else if header = (2 : Fin 256) then
      (yPayload.decode tail).map fun result => (tableOfY result.1, result.2)
    else if header = (3 : Fin 256) then
      (zPayload.decode tail).map fun result => (tableOfZ result.1, result.2)
    else
      biquadraticFallback.decode tail

/-- The three field/digit-row present/absent shapes `Biquadratic.garbleX/Y/Z` produce
(`Construction/ArgoMAC/Biquadratic.lean`), each carried by a one-byte header instead of an
option tag per field. Every other `Biquadratic.Table` falls back to `biquadraticFallback`
behind header byte `0`, so the encoding stays total. -/
def biquadratic : Encoding Biquadratic.Table where
  encode := encodeBiquadratic
  decode := decodeBiquadratic
  decode_encode value tail := by
    cases hX : xPayloadOf value with
    | some payload =>
      have restored := tableOfX_payloadOf value payload hX
      simp [encodeBiquadratic, decodeBiquadratic, hX, restored, xPayload.decode_encode]
    | none =>
      cases hY : yPayloadOf value with
      | some payload =>
        have restored := tableOfY_payloadOf value payload hY
        simp [encodeBiquadratic, decodeBiquadratic, hX, hY, restored, yPayload.decode_encode]
      | none =>
        cases hZ : zPayloadOf value with
        | some payload =>
          have restored := tableOfZ_payloadOf value payload hZ
          simp [encodeBiquadratic, decodeBiquadratic, hX, hY, hZ, restored,
            zPayload.decode_encode]
        | none =>
          simp [encodeBiquadratic, decodeBiquadratic, hX, hY, hZ,
            biquadraticFallback.decode_encode]

def pointMAC : Encoding FieldMacToECMac.Table :=
  let rows := biquadratic.vector FieldMacToECMac.outputMacCount
  (rows.pair (rows.pair rows)).map
    (fun value => (value.x, value.y, value.z))
    (fun ⟨x, y, z⟩ => ⟨x, y, z⟩)
    (fun _ => rfl)

/-- This encoding includes every public field and, per `pointMAC` row, one header byte. -/
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

@[simp] private theorem x_length (c0 c1 c2 c3 c5 : BaseField)
    (randomness : Biquadratic.XRandomness) (oracles : Biquadratic.Oracles) (key : InputMacKey) :
    (biquadratic.encode (Biquadratic.garbleX c0 c1 c2 c3 c5 randomness oracles key)).length =
      32673 := by
  simp [biquadratic, encodeBiquadratic, xPayloadOf,
    Biquadratic.garbleX, xPayload, Encoding.map, Encoding.pair]

@[simp] private theorem y_length (c0 c1 c4 c5 : BaseField)
    (randomness : Biquadratic.YRandomness) (oracles : Biquadratic.Oracles) (key : InputMacKey) :
    (biquadratic.encode (Biquadratic.garbleY c0 c1 c4 c5 randomness oracles key)).length =
      32641 := by
  simp [biquadratic, encodeBiquadratic, xPayloadOf, yPayloadOf,
    Biquadratic.garbleY, yPayload, Encoding.map, Encoding.pair]

@[simp] private theorem z_length (c0 c2 c3 c4 c5 : BaseField)
    (randomness : Biquadratic.ZRandomness) (oracles : Biquadratic.Oracles) (key : InputMacKey) :
    (biquadratic.encode (Biquadratic.garbleZ c0 c2 c3 c4 c5 randomness oracles key)).length =
      40801 := by
  simp [biquadratic, encodeBiquadratic, xPayloadOf, yPayloadOf, zPayloadOf,
    Biquadratic.garbleZ, zPayload, Encoding.map, Encoding.pair]

/-- The exact bytes of an X-shaped row, stated on the literal shape so callers outside
`Construction` (which cannot see `xPayloadOf`) can rewrite with it. -/
theorem biquadratic_encode_x (c0 c1 c2 c3 c5 : BaseField)
    (x9 y6 y8 y10 : Vector BitAdaptor.Table coordinateBitCount) :
    biquadratic.encode ⟨some c0, some c1, some c2, some c3, none, some c5,
        none, some x9, some y6, some y8, some y10⟩ =
      (1 : Fin 256) :: (field.encode c0 ++ field.encode c1 ++ field.encode c2 ++
        field.encode c3 ++ field.encode c5 ++
        digit.encode x9 ++ digit.encode y6 ++ digit.encode y8 ++ digit.encode y10) := by
  simp [biquadratic, encodeBiquadratic, xPayloadOf, xPayload, Encoding.map, Encoding.pair]

/-- The exact bytes of a Y-shaped row, stated on the literal shape. -/
theorem biquadratic_encode_y (c0 c1 c4 c5 : BaseField)
    (x7 x9 y8 y10 : Vector BitAdaptor.Table coordinateBitCount) :
    biquadratic.encode ⟨some c0, some c1, none, none, some c4, some c5,
        some x7, some x9, none, some y8, some y10⟩ =
      (2 : Fin 256) :: (field.encode c0 ++ field.encode c1 ++ field.encode c4 ++
        field.encode c5 ++
        digit.encode x7 ++ digit.encode x9 ++ digit.encode y8 ++ digit.encode y10) := by
  simp [biquadratic, encodeBiquadratic, xPayloadOf, yPayloadOf, yPayload, Encoding.map,
    Encoding.pair]

/-- The exact bytes of a Z-shaped row, stated on the literal shape. -/
theorem biquadratic_encode_z (c0 c2 c3 c4 c5 : BaseField)
    (x7 x9 y6 y8 y10 : Vector BitAdaptor.Table coordinateBitCount) :
    biquadratic.encode ⟨some c0, none, some c2, some c3, some c4, some c5,
        some x7, some x9, some y6, some y8, some y10⟩ =
      (3 : Fin 256) :: (field.encode c0 ++ field.encode c2 ++ field.encode c3 ++
        field.encode c4 ++ field.encode c5 ++
        digit.encode x7 ++ digit.encode x9 ++ digit.encode y6 ++ digit.encode y8 ++
        digit.encode y10) := by
  simp [biquadratic, encodeBiquadratic, xPayloadOf, yPayloadOf, zPayloadOf, zPayload,
    Encoding.map, Encoding.pair]

private theorem pointMAC_length (rows : FieldMacToECMac.Rows)
    (randomness : FieldMacToECMac.Randomness) (oracles : FieldMacToECMac.Oracles) (key : InputMacKey) :
    (pointMAC.encode (FieldMacToECMac.garble rows randomness oracles key)).length = 9762580 := by
  simp only [pointMAC, Encoding.map, Encoding.pair, List.length_append]
  rw [Encoding.vector_length biquadratic 32673 _ _ (by
        intro index; simp [FieldMacToECMac.garble, FieldMacToECMac.garbleRow]),
      Encoding.vector_length biquadratic 32641 _ _ (by
        intro index; simp [FieldMacToECMac.garble, FieldMacToECMac.garbleRow]),
      Encoding.vector_length biquadratic 40801 _ _ (by
        intro index; simp [FieldMacToECMac.garble, FieldMacToECMac.garbleRow])]
  rfl

/-- Every scalar and random tape produces the same complete ciphertext length. -/
theorem garble_length (construction : Construction) (scalar : NonZeroScalar)
    (randomness : Garbling.Randomness) :
    (encoding.encode (Garbling.garble construction scalar randomness).1).length = 9803316 := by
  simp [encoding, Encoding.map, Encoding.pair, Garbling.garble, Pipeline.garble, pointMAC_length]

end Wire
end Kriterion.ArgoMAC
