import Construction.TruncatedPipeline
import Construction.TruncatedPointSchema
import Construction.Garbling

namespace Kriterion.ArgoMAC.TruncatedPipeline.Wire

open BN254

abbrev Triple :=
  TruncatedBiquadratic.Table × TruncatedBiquadratic.Table × TruncatedBiquadratic.Table

private def toPublic (tables : Triple) : TruncatedPointEncoding.PublicTriple :=
  match TruncatedPointSchema.generated? tables.1 tables.2.1 tables.2.2 with
  | some value => .generated value
  | none => .fallback tables

private def ofPublic : TruncatedPointEncoding.PublicTriple → Triple
  | .generated value => TruncatedPointSchema.tablesOf value
  | .fallback tables => tables

private theorem ofPublic_toPublic (tables : Triple) : ofPublic (toPublic tables) = tables := by
  rcases tables with ⟨x, y, z⟩
  cases encoded : TruncatedPointSchema.generated? x y z with
  | some value =>
    simp only [toPublic, encoded, ofPublic]
    exact TruncatedPointSchema.tablesOf_generated x y z value encoded
  | none => simp only [toPublic, encoded, ofPublic]

/-- The generated layout takes 97,218 bytes. Every other layout keeps the fallback codec. -/
private def triple : Encoding Triple :=
  TruncatedPointEncoding.publicEncoding.map toPublic ofPublic ofPublic_toPublic

private def groupedRows (value : TruncatedFieldMacToECMac.Table) :
    Vector Triple FieldMacToECMac.outputMacCount :=
  Vector.ofFn fun index => (value.x.get index, value.y.get index, value.z.get index)

private def tablesOfRows (rows : Vector Triple FieldMacToECMac.outputMacCount) :
    TruncatedFieldMacToECMac.Table :=
  { x := Vector.ofFn fun index => (rows.get index).1
    y := Vector.ofFn fun index => (rows.get index).2.1
    z := Vector.ofFn fun index => (rows.get index).2.2 }

private theorem vector_ofFn_get {Value : Type} {count : Nat} (values : Vector Value count) :
    Vector.ofFn (fun index => values.get index) = values := by
  apply Vector.ext
  intro index inRange
  simp only [Vector.getElem_ofFn]
  rfl

private theorem tablesOfRows_groupedRows (value : TruncatedFieldMacToECMac.Table) :
    tablesOfRows (groupedRows value) = value := by
  rcases value with ⟨x, y, z⟩
  simp only [tablesOfRows, groupedRows, Vector.get_ofFn]
  rw [vector_ofFn_get x, vector_ofFn_get y, vector_ofFn_get z]

private def pointMAC : Encoding TruncatedFieldMacToECMac.Table :=
  (triple.vector FieldMacToECMac.outputMacCount).map groupedRows tablesOfRows
    tablesOfRows_groupedRows

/-- The curve codec is a parameter, so no proof unfolds the large joint curve codec. -/
def encoding (curve : Encoding TruncatedCurveMembership.Table) : Encoding Table :=
  (curve.pair pointMAC).map
    (fun value => (value.curve, value.pointMAC))
    (fun ⟨curve, pointMAC⟩ => ⟨curve, pointMAC⟩)
    (fun _ => rfl)

private theorem tripleRow_length (rows : Coordinates.Rows)
    (randomness : FieldMacToECMac.RowRandomness) (oracles : FieldMacToECMac.RowOracles)
    (key : InputMacKey) :
    (triple.encode
      (TruncatedBiquadratic.project (FieldMacToECMac.garbleRow rows randomness oracles key).x,
       TruncatedBiquadratic.project (FieldMacToECMac.garbleRow rows randomness oracles key).y,
       TruncatedBiquadratic.project (FieldMacToECMac.garbleRow rows randomness oracles key).z)).length =
      97218 := by
  simp [triple, Encoding.map, toPublic, TruncatedPointSchema.generated?,
    TruncatedBiquadratic.project, TruncatedBiquadratic.projectDigit,
    FieldMacToECMac.garbleRow, Biquadratic.garbleX, Biquadratic.garbleY, Biquadratic.garbleZ,
    TruncatedPointEncoding.publicEncoding, TruncatedPointEncoding.generatedEncoding_length]

private theorem pointMAC_length (rows : FieldMacToECMac.Rows)
    (randomness : FieldMacToECMac.Randomness) (oracles : FieldMacToECMac.Oracles) (key : InputMacKey) :
    (pointMAC.encode (TruncatedFieldMacToECMac.project
      (FieldMacToECMac.garble rows randomness oracles key))).length = 8846838 := by
  simp only [pointMAC, Encoding.map]
  rw [Encoding.vector_length triple 97218 _ _ (by
        intro index
        simpa [groupedRows, TruncatedFieldMacToECMac.project, FieldMacToECMac.garble] using
          tripleRow_length (rows.get index) (randomness.get index) (oracles.get index) key)]
  rfl

/-- Every scalar and random tape produces the same complete projected ciphertext length. -/
theorem garble_length (curve : Encoding TruncatedCurveMembership.Table) (curveBytes : Nat)
    (curveLength : ∀ table, (curve.encode table).length = curveBytes)
    (construction : Construction) (scalar : NonZeroScalar) (randomness : Garbling.Randomness) :
    ((encoding curve).encode (project (Garbling.garble construction scalar randomness).1)).length =
      curveBytes + 8846838 := by
  simp [encoding, Encoding.map, Encoding.pair, project, Garbling.garble, Pipeline.garble,
    pointMAC_length, curveLength]

end Kriterion.ArgoMAC.TruncatedPipeline.Wire
