import Construction.ArgoMAC.FieldPacking
import Construction.TruncatedBiquadratic
import Construction.BitRowPacking
import Construction.FourRowPacking
import Encoding

namespace Kriterion.ArgoMAC.TruncatedPointEncoding

open BN254

/-- The generated point triple has fourteen coefficients and twelve digit rows. -/
structure GeneratedTriple where
  coefficients : Fin 14 → BaseField
  rows : Fin 3048 → BitVec 254

private def payload (value : GeneratedTriple) :
    (Fin 14 → BaseField) × (Fin 3048 → BitVec 254) :=
  (value.coefficients, value.rows)

private def restore (value : (Fin 14 → BaseField) × (Fin 3048 → BitVec 254)) :
    GeneratedTriple :=
  ⟨value.1, value.2⟩

private theorem restore_payload (value : GeneratedTriple) : restore (payload value) = value := by
  cases value
  rfl

/-- A block holds four rows. The twelve rows form 762 complete blocks. -/
def generatedEncoding : Encoding GeneratedTriple :=
  (FieldPacking.fourteen.pair (FourRowPacking.encoding 762)).map payload restore restore_payload

theorem generatedEncoding_length (value : GeneratedTriple) :
    (generatedEncoding.encode value).length = 97218 := by
  simp only [generatedEncoding, Encoding.map, Encoding.pair, payload, List.length_append]
  rw [FieldPacking.fourteen_length, FourRowPacking.encoding_length]

/-- This fallback preserves every optional adaptor layout. -/
private def field : Encoding BaseField :=
  (Encoding.natural 32).map
    (fun value => ⟨value.val, lt_trans value.val_lt (by decide)⟩)
    (fun value => value.val)
    (fun value => ZMod.natCast_zmod_val value)

private def row : Encoding TruncatedBitAdaptor.Table :=
  (BitRowPacking.encoding 254 1 32 (by decide)).map
    (fun value => fun _ => value.trueRow)
    (fun value => ⟨value 0⟩)
    (fun value => by cases value; rfl)

private def digit : Encoding (Vector TruncatedBitAdaptor.Table coordinateBitCount) :=
  Encoding.vector row coordinateBitCount

private def biquadratic : Encoding TruncatedBiquadratic.Table :=
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

abbrev FallbackTriple :=
  TruncatedBiquadratic.Table × TruncatedBiquadratic.Table × TruncatedBiquadratic.Table

private def fallback : Encoding FallbackTriple :=
  (biquadratic.pair (biquadratic.pair biquadratic)).map
    (fun value => (value.1, value.2.1, value.2.2))
    (fun ⟨x, y, z⟩ => (x, (y, z)))
    (fun _ => rfl)

/-- Generated triples use the leading-byte range of fourteen field elements.
The `fallback` branch preserves every other optional-table layout. -/
inductive PublicTriple where
  | generated (value : GeneratedTriple)
  | fallback (value : FallbackTriple)

def publicEncoding : Encoding PublicTriple where
  encode
    | .generated value => generatedEncoding.encode value
    | .fallback value => 255 :: fallback.encode value
  decode bytes := match bytes with
    | [] => none
    | 255 :: tail => (fallback.decode tail).map fun value => (.fallback value.1, value.2)
    | _ => (generatedEncoding.decode bytes).map fun value => (.generated value.1, value.2)
  decode_encode value tail := by
    cases value with
    | generated value =>
        change (match generatedEncoding.encode value ++ tail with
          | [] => none
          | 255 :: rest => (fallback.decode rest).map fun result =>
            (PublicTriple.fallback result.1, result.2)
          | _ => (generatedEncoding.decode (generatedEncoding.encode value ++ tail)).map
            fun result => (PublicTriple.generated result.1, result.2)) =
              some (PublicTriple.generated value, tail)
        obtain ⟨first, coefficientTail, leading, notMarker⟩ :=
          FieldPacking.fourteen_prefix value.coefficients
        rw [show generatedEncoding.encode value = first :: coefficientTail ++
          (FourRowPacking.encoding 762).encode value.rows by
          simp only [generatedEncoding, Encoding.map, Encoding.pair, payload, leading]]
        have decoded : generatedEncoding.decode
            (first :: (coefficientTail ++ ((FourRowPacking.encoding 762).encode value.rows ++ tail))) =
            some (value, tail) := by
          have bytes : first :: (coefficientTail ++
              ((FourRowPacking.encoding 762).encode value.rows ++ tail)) =
              generatedEncoding.encode value ++ tail := by
            simp only [generatedEncoding, Encoding.map, Encoding.pair, payload,
              leading, List.cons_append, List.append_assoc]
          rw [bytes]
          exact generatedEncoding.decode_encode value tail
        simpa [notMarker] using congrArg (Option.map fun result =>
          (PublicTriple.generated result.1, result.2)) decoded
    | fallback value =>
        simp [fallback.decode_encode]

end Kriterion.ArgoMAC.TruncatedPointEncoding
