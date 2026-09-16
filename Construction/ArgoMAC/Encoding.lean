import Construction.Garbling
import Construction.ArgoMAC.FieldPacking
import Encoding

namespace Kriterion.ArgoMAC

open BN254

namespace Wire

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

private def biquadratic : Encoding Biquadratic.Table :=
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

private structure TriplePayload where
  xc0 : BaseField
  xc1 : BaseField
  xc2 : BaseField
  xc3 : BaseField
  xc5 : BaseField
  yc0 : BaseField
  yc1 : BaseField
  yc4 : BaseField
  yc5 : BaseField
  zc0 : BaseField
  zc2 : BaseField
  zc3 : BaseField
  zc4 : BaseField
  zc5 : BaseField
  xx9 : Vector BitAdaptor.Table coordinateBitCount
  xy6 : Vector BitAdaptor.Table coordinateBitCount
  xy8 : Vector BitAdaptor.Table coordinateBitCount
  xy10 : Vector BitAdaptor.Table coordinateBitCount
  yx7 : Vector BitAdaptor.Table coordinateBitCount
  yx9 : Vector BitAdaptor.Table coordinateBitCount
  yy8 : Vector BitAdaptor.Table coordinateBitCount
  zx7 : Vector BitAdaptor.Table coordinateBitCount
  zx9 : Vector BitAdaptor.Table coordinateBitCount
  zy6 : Vector BitAdaptor.Table coordinateBitCount
  zy8 : Vector BitAdaptor.Table coordinateBitCount
  zy10 : Vector BitAdaptor.Table coordinateBitCount

private def tripleFields (value : TriplePayload) : Fin 14 → BaseField :=
  (#v[value.xc0, value.xc1, value.xc2, value.xc3, value.xc5,
    value.yc0, value.yc1, value.yc4, value.yc5,
    value.zc0, value.zc2, value.zc3, value.zc4, value.zc5]).get

private def tripleDigits :=
  let d1 := digit.pair digit
  let d2 := digit.pair d1
  let d3 := digit.pair d2
  let d4 := digit.pair d3
  let d5 := digit.pair d4
  let d6 := digit.pair d5
  let d7 := digit.pair d6
  let d8 := digit.pair d7
  let d9 := digit.pair d8
  let d10 := digit.pair d9
  let d11 := digit.pair d10
  d11

private def triplePayload : Encoding TriplePayload :=
  Encoding.map
    (FieldPacking.fourteen.pair tripleDigits)
    (fun value => (tripleFields value,
      value.xx9, value.xy6, value.xy8, value.xy10,
      value.yx7, value.yx9, value.yy8,
      value.zx7, value.zx9, value.zy6, value.zy8, value.zy10))
    (fun ⟨fields, xx9, xy6, xy8, xy10, yx7, yx9, yy8, zx7, zx9, zy6, zy8, zy10⟩ =>
      ⟨fields 0, fields 1, fields 2, fields 3, fields 4,
        fields 5, fields 6, fields 7, fields 8,
        fields 9, fields 10, fields 11, fields 12, fields 13,
        xx9, xy6, xy8, xy10, yx7, yx9, yy8, zx7, zx9, zy6, zy8, zy10⟩)
    (fun _ => rfl)

private def tablesOfTriple (value : TriplePayload) :
    Biquadratic.Table × Biquadratic.Table × Biquadratic.Table :=
  ( { c0 := some value.xc0, c1 := some value.xc1, c2 := some value.xc2,
      c3 := some value.xc3, c4 := none, c5 := some value.xc5,
      x7 := none, x9 := some value.xx9, y6 := some value.xy6,
      y8 := some value.xy8, y10 := some value.xy10 },
    { c0 := some value.yc0, c1 := some value.yc1, c2 := none, c3 := none,
      c4 := some value.yc4, c5 := some value.yc5,
      x7 := some value.yx7, x9 := some value.yx9, y6 := none,
      y8 := some value.yy8, y10 := none },
    { c0 := some value.zc0, c1 := none, c2 := some value.zc2,
      c3 := some value.zc3, c4 := some value.zc4, c5 := some value.zc5,
      x7 := some value.zx7, x9 := some value.zx9, y6 := some value.zy6,
      y8 := some value.zy8, y10 := some value.zy10 } )

private def triplePayloadOf (tables :
    Biquadratic.Table × Biquadratic.Table × Biquadratic.Table) : Option TriplePayload :=
  match tables.1.c0, tables.1.c1, tables.1.c2, tables.1.c3, tables.1.c4, tables.1.c5,
      tables.1.x7, tables.1.x9, tables.1.y6, tables.1.y8, tables.1.y10,
      tables.2.1.c0, tables.2.1.c1, tables.2.1.c2, tables.2.1.c3, tables.2.1.c4, tables.2.1.c5,
      tables.2.1.x7, tables.2.1.x9, tables.2.1.y6, tables.2.1.y8, tables.2.1.y10,
      tables.2.2.c0, tables.2.2.c1, tables.2.2.c2, tables.2.2.c3, tables.2.2.c4, tables.2.2.c5,
      tables.2.2.x7, tables.2.2.x9, tables.2.2.y6, tables.2.2.y8, tables.2.2.y10 with
  | some xc0, some xc1, some xc2, some xc3, none, some xc5,
      none, some xx9, some xy6, some xy8, some xy10,
      some yc0, some yc1, none, none, some yc4, some yc5,
      some yx7, some yx9, none, some yy8, none,
      some zc0, none, some zc2, some zc3, some zc4, some zc5,
      some zx7, some zx9, some zy6, some zy8, some zy10 =>
      some ⟨xc0, xc1, xc2, xc3, xc5, yc0, yc1, yc4, yc5, zc0, zc2, zc3, zc4, zc5,
        xx9, xy6, xy8, xy10, yx7, yx9, yy8, zx7, zx9, zy6, zy8, zy10⟩
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none

private theorem tablesOfTriple_payloadOf (tables :
    Biquadratic.Table × Biquadratic.Table × Biquadratic.Table) (payload : TriplePayload)
    (encoded : triplePayloadOf tables = some payload) : tablesOfTriple payload = tables := by
  rcases tables with ⟨x, y, z⟩
  rcases x with ⟨xc0, xc1, xc2, xc3, xc4, xc5, xx7, xx9, xy6, xy8, xy10⟩
  rcases y with ⟨yc0, yc1, yc2, yc3, yc4, yc5, yx7, yx9, yy6, yy8, yy10⟩
  rcases z with ⟨zc0, zc1, zc2, zc3, zc4, zc5, zx7, zx9, zy6, zy8, zy10⟩
  unfold triplePayloadOf at encoded
  split at encoded
  · injection encoded with encoded
    subst payload
    simp_all [tablesOfTriple]
  · simp_all

private def genericTriple : Encoding
    (Biquadratic.Table × Biquadratic.Table × Biquadratic.Table) :=
  (biquadratic.pair (biquadratic.pair biquadratic)).map
    (fun value => (value.1, value.2.1, value.2.2))
    (fun ⟨x, y, z⟩ => (x, y, z))
    (fun _ => rfl)

private theorem triplePayload_prefix (value : TriplePayload) :
    ∃ first tail, triplePayload.encode value = first :: tail ∧ first ≠ 255 := by
  rcases FieldPacking.fourteen_prefix (tripleFields value) with ⟨first, fieldsTail, leading, notMarker⟩
  refine ⟨first, fieldsTail ++
    digit.encode value.xx9 ++ digit.encode value.xy6 ++ digit.encode value.xy8 ++ digit.encode value.xy10 ++
    digit.encode value.yx7 ++ digit.encode value.yx9 ++ digit.encode value.yy8 ++
    digit.encode value.zx7 ++ digit.encode value.zx9 ++ digit.encode value.zy6 ++ digit.encode value.zy8 ++
    digit.encode value.zy10, ?_, notMarker⟩
  simp only [triplePayload, tripleDigits, Encoding.map, Encoding.pair]
  rw [leading]
  simp

private def encodeTriple (tables : Biquadratic.Table × Biquadratic.Table × Biquadratic.Table) :
    List (Fin 256) :=
  match triplePayloadOf tables with
  | some payload => triplePayload.encode payload
  | none => 255 :: genericTriple.encode tables

private def decodeTriple (bytes : List (Fin 256)) :
    Option ((Biquadratic.Table × Biquadratic.Table × Biquadratic.Table) × List (Fin 256)) :=
  match bytes with
  | 255 :: tail => genericTriple.decode tail
  | _ => (triplePayload.decode bytes).map fun result => (tablesOfTriple result.1, result.2)

private def groupedBiquadratic : Encoding
    (Biquadratic.Table × Biquadratic.Table × Biquadratic.Table) where
  encode := encodeTriple
  decode := decodeTriple
  decode_encode tables tail := by
    cases encoded : triplePayloadOf tables with
    | some payload =>
      have restored := tablesOfTriple_payloadOf tables payload encoded
      rcases triplePayload_prefix payload with ⟨first, prefixTail, leading, notMarker⟩
      have decoded := triplePayload.decode_encode payload tail
      rw [leading] at decoded
      have mapped := congrArg (Option.map fun result => (tablesOfTriple result.1, result.2)) decoded
      simpa [encodeTriple, decodeTriple, encoded, leading, notMarker, restored] using mapped
    | none =>
      simp [encodeTriple, decodeTriple, encoded, genericTriple.decode_encode]

private def groupedRows (value : FieldMacToECMac.Table) :
    Vector (Biquadratic.Table × Biquadratic.Table × Biquadratic.Table) FieldMacToECMac.outputMacCount :=
  Vector.ofFn fun index => (value.x.get index, value.y.get index, value.z.get index)

private def tablesOfRows (rows :
    Vector (Biquadratic.Table × Biquadratic.Table × Biquadratic.Table) FieldMacToECMac.outputMacCount) :
    FieldMacToECMac.Table :=
  { x := Vector.ofFn fun index => (rows.get index).1
    y := Vector.ofFn fun index => (rows.get index).2.1
    z := Vector.ofFn fun index => (rows.get index).2.2 }

private theorem vector_ofFn_get {Value : Type} {count : Nat} (values : Vector Value count) :
    Vector.ofFn (fun index => values.get index) = values := by
  apply Vector.ext
  intro index inRange
  simp only [Vector.getElem_ofFn]
  rfl

private theorem tablesOfRows_groupedRows (value : FieldMacToECMac.Table) :
    tablesOfRows (groupedRows value) = value := by
  rcases value with ⟨x, y, z⟩
  simp only [tablesOfRows, groupedRows, Vector.get_ofFn]
  rw [vector_ofFn_get x, vector_ofFn_get y, vector_ofFn_get z]

private def pointMAC : Encoding FieldMacToECMac.Table :=
  (groupedBiquadratic.vector FieldMacToECMac.outputMacCount).map
    groupedRows tablesOfRows
    tablesOfRows_groupedRows

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

@[simp] private theorem curve_length (value : CurveMembership.Table) :
    (curve.encode value).length = 40736 := by
  simp [curve, Encoding.map, Encoding.pair]

@[simp] private theorem coefficient_length (value : Option BaseField) :
    (field.option.encode value).length = if value.isSome then 33 else 1 := by
  cases value <;> simp [Encoding.option]

@[simp] private theorem rows_length (value : Option (Vector BitAdaptor.Table coordinateBitCount)) :
    (digit.option.encode value).length = if value.isSome then 8129 else 1 := by
  cases value <;> simp [Encoding.option]

private theorem biquadratic_length (value : Biquadratic.Table) :
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
    (biquadratic.encode (Biquadratic.garbleY c0 c1 c4 c5 randomness oracles key)).length = 24523 := by
  rw [biquadratic_length]
  simp [Biquadratic.garbleY]

@[simp] private theorem z_length (c0 c2 c3 c4 c5 : BaseField)
    (randomness : Biquadratic.ZRandomness) (oracles : Biquadratic.Oracles) (key : InputMacKey) :
    (biquadratic.encode (Biquadratic.garbleZ c0 c2 c3 c4 c5 randomness oracles key)).length = 40811 := by
  rw [biquadratic_length]
  simp [Biquadratic.garbleZ]

private theorem groupedRow_length (rows : Coordinates.Rows)
    (randomness : FieldMacToECMac.RowRandomness) (oracles : FieldMacToECMac.RowOracles)
    (key : InputMacKey) :
    (groupedBiquadratic.encode
      ((FieldMacToECMac.garbleRow rows randomness oracles key).x,
       (FieldMacToECMac.garbleRow rows randomness oracles key).y,
       (FieldMacToECMac.garbleRow rows randomness oracles key).z)).length = 97980 := by
  simp [groupedBiquadratic, encodeTriple, triplePayloadOf,
    FieldMacToECMac.garbleRow, Biquadratic.garbleX, Biquadratic.garbleY, Biquadratic.garbleZ,
    triplePayload, tripleDigits, Encoding.map, Encoding.pair]

private theorem pointMAC_length (rows : FieldMacToECMac.Rows)
    (randomness : FieldMacToECMac.Randomness) (oracles : FieldMacToECMac.Oracles) (key : InputMacKey) :
    (pointMAC.encode (FieldMacToECMac.garble rows randomness oracles key)).length = 8916180 := by
  simp only [pointMAC, Encoding.map]
  rw [Encoding.vector_length groupedBiquadratic 97980 _ _ (by
        intro index
        simpa [groupedRows, FieldMacToECMac.garble] using
          groupedRow_length (rows.get index) (randomness.get index) (oracles.get index) key)]
  rfl

/-- Every scalar and random tape produces the same complete ciphertext length. -/
theorem garble_length (construction : Construction) (scalar : NonZeroScalar)
    (randomness : Garbling.Randomness) :
    (encoding.encode (Garbling.garble construction scalar randomness).1).length = 8956916 := by
  simp [encoding, Encoding.map, Encoding.pair, Garbling.garble, Pipeline.garble, pointMAC_length]

end Wire
end Kriterion.ArgoMAC
