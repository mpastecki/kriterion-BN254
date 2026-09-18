import Construction.TruncatedCurveMembership
import Construction.ArgoMAC.FieldPacking
import Construction.BitRowPacking
import Encoding

namespace Kriterion.ArgoMAC.TruncatedCurveMembership.JointWire

open BN254

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
  intro index inRange
  simp only [unpackRows, packRows, Vector.getElem_ofFn, Equiv.symm_apply_apply]
  rfl

private def fields (table : Table) : Fin 3 → BaseField := #v[table.c0, table.c1, table.c2].get

private def restore (value : (Fin 3 → BaseField) × (Fin 1270 → BitVec 254)) : Table :=
  ⟨value.1 0, value.1 1, value.1 2,
    unpackRows value.2 0, unpackRows value.2 1, unpackRows value.2 2,
    unpackRows value.2 3, unpackRows value.2 4⟩

private theorem restore_payload (table : Table) : restore (fields table, packRows table) = table := by
  simp only [restore, fields, unpack_pack]
  rfl

set_option exponentiation.threshold 800 in
private theorem field_capacity : baseFieldModulus ^ 3 ≤ 2 ^ 762 := by
  norm_num [baseFieldModulus]

private theorem joint_capacity :
    baseFieldModulus ^ 3 * ((2 ^ 254) ^ 1270) ≤ 256 ^ 40418 := by
  rw [← pow_mul]
  calc
    baseFieldModulus ^ 3 * 2 ^ (254 * 1270) ≤ 2 ^ 762 * 2 ^ (254 * 1270) :=
      Nat.mul_le_mul_right _ field_capacity
    _ = 2 ^ (762 + 254 * 1270) := by rw [← pow_add]
    _ ≤ 2 ^ (8 * 40418) := by
      apply Nat.pow_le_pow_right (by decide)
      norm_num
    _ = 256 ^ 40418 := by
      rw [show 256 = 2 ^ 8 by norm_num, ← pow_mul]

private def narrow (bound bytes : Nat) [NeZero bound] (fits : bound ≤ 256 ^ bytes) :
    Encoding (Fin bound) :=
  (Encoding.natural bytes).map (fun value => value.castLE fits)
    (fun value => Fin.ofNat bound value.val) (fun value => Fin.ofNat_val_eq_self value)

private theorem narrow_length (bound bytes : Nat) [NeZero bound] (fits : bound ≤ 256 ^ bytes)
    (value : Fin bound) : ((narrow bound bytes fits).encode value).length = bytes := by
  simp only [narrow, Encoding.map, Encoding.natural_length]

private def mapped {A : Type} (bound bytes : Nat) [NeZero bound]
    (fits : bound ≤ 256 ^ bytes) (forward : A → Fin bound) (backward : Fin bound → A)
    (inverse : ∀ value, backward (forward value) = value) : Encoding A :=
  (narrow bound bytes fits).map forward backward inverse

private theorem mapped_length {A : Type} (bound bytes : Nat) [NeZero bound]
    (fits : bound ≤ 256 ^ bytes) (forward : A → Fin bound) (backward : Fin bound → A)
    (inverse : ∀ value, backward (forward value) = value) (value : A) :
    ((mapped bound bytes fits forward backward inverse).encode value).length = bytes :=
  narrow_length bound bytes fits (forward value)

private def pairEquiv : ((Fin 3 → BaseField) × (Fin 1270 → BitVec 254)) ≃
    Fin (baseFieldModulus ^ 3 * ((2 ^ 254) ^ 1270)) :=
  ((FieldPacking.digitsEquiv 3).prodCongr (BitRowPacking.digitsEquiv 254 1270)).trans finProdFinEquiv

private def packedTable (table : Table) : Fin (baseFieldModulus ^ 3 * ((2 ^ 254) ^ 1270)) :=
  pairEquiv (fields table, packRows table)

private def unpackTable (value : Fin (baseFieldModulus ^ 3 * ((2 ^ 254) ^ 1270))) : Table :=
  restore (pairEquiv.symm value)

private theorem table_inverse (table : Table) : unpackTable (packedTable table) = table := by
  simp only [unpackTable, packedTable, Equiv.symm_apply_apply, restore_payload]

/-- Complete joint codec for every field coefficient, row, and trailing byte list. -/
def encoding : Encoding Table :=
  mapped _ 40418 joint_capacity packedTable unpackTable table_inverse

theorem encoding_length (table : Table) : (encoding.encode table).length = 40418 :=
  mapped_length _ 40418 joint_capacity packedTable unpackTable table_inverse table

end Kriterion.ArgoMAC.TruncatedCurveMembership.JointWire
