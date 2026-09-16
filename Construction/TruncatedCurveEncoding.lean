import Construction.TruncatedCurveMembership
import Construction.BitRowPacking

namespace Kriterion.ArgoMAC.TruncatedCurveMembership.Wire
open BN254

private def field : Encoding BaseField :=
  (Encoding.natural 32).map
    (fun value => ⟨value.val, lt_trans value.val_lt (by decide)⟩)
    (fun value => value.val)
    (fun value => ZMod.natCast_zmod_val value)

private def rows (table : Table) : Vector (Vector TruncatedBitAdaptor.Table 254) 5 :=
  #v[table.x3, table.x5, table.x7, table.y4, table.y6]

private def packRows (table : Table) : Fin 1270 → BitVec 254 := fun index =>
  let location := (finProdFinEquiv : Fin 5 × Fin 254 ≃ Fin 1270).symm index
  (((rows table).get location.1).get location.2).trueRow

private def unpackRows (packed : Fin 1270 → BitVec 254) (kind : Fin 5) :
    Vector TruncatedBitAdaptor.Table 254 :=
  Vector.ofFn fun position => ⟨packed (finProdFinEquiv (kind, position))⟩

private theorem unpack_pack (table : Table) (kind : Fin 5) :
    unpackRows (packRows table) kind = (rows table).get kind := by
  apply Vector.ext
  intro index bound
  simp only [unpackRows, packRows, Vector.getElem_ofFn, Equiv.symm_apply_apply]
  rfl

private def payload (table : Table) : BaseField × BaseField × BaseField × (Fin 1270 → BitVec 254) :=
  (table.c0, table.c1, table.c2, packRows table)

private def restore (value : BaseField × BaseField × BaseField × (Fin 1270 → BitVec 254)) : Table :=
  ⟨value.1, value.2.1, value.2.2.1,
    unpackRows value.2.2.2 0, unpackRows value.2.2.2 1, unpackRows value.2.2.2 2,
    unpackRows value.2.2.2 3, unpackRows value.2.2.2 4⟩

private theorem restore_payload (table : Table) : restore (payload table) = table := by
  simp only [restore, payload, unpack_pack]
  rfl

/-- Complete smaller public table: three field coefficients followed by dense rows. -/
def encoding : Encoding Table :=
  (field.pair (field.pair (field.pair BitRowPacking.curveRows))).map payload restore restore_payload

@[simp] private theorem field_length (value : BaseField) : (field.encode value).length = 32 := by
  simp [field, Encoding.map]

theorem encoding_length (table : Table) : (encoding.encode table).length = 40419 := by
  simp [encoding, Encoding.map, Encoding.pair]

end Kriterion.ArgoMAC.TruncatedCurveMembership.Wire
