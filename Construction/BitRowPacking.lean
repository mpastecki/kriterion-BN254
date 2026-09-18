import Encoding
import Mathlib.Data.BitVec
import Mathlib.Algebra.BigOperators.Fin

namespace Kriterion.BitRowPacking

/-- Explicit binary-radix packing of fixed-width public rows. -/
def digitsEquiv (width count : Nat) :
    (Fin count → BitVec width) ≃ Fin ((2 ^ width) ^ count) :=
  (Equiv.piCongrRight fun _ => BitVec.equivFin.toEquiv).trans finFunctionFinEquiv

theorem capacity (width count bytes : Nat) (fits : width * count ≤ 8 * bytes) :
    (2 ^ width) ^ count ≤ 256 ^ bytes := by
  rw [← pow_mul]
  change 2 ^ (width * count) ≤ (2 ^ 8) ^ bytes
  rw [← pow_mul]
  exact Nat.pow_le_pow_right (by decide) fits

/-- The decoder recovers every public row and the exact trailing byte list. -/
def encoding (width count bytes : Nat) (fits : width * count ≤ 8 * bytes) :
    Encoding (Fin count → BitVec width) :=
  let packed : Encoding (Fin ((2 ^ width) ^ count)) :=
    (Encoding.natural bytes).map
      (fun value => value.castLE (capacity width count bytes fits))
      (fun value => Fin.ofNat ((2 ^ width) ^ count) value.val)
      (fun value => Fin.ofNat_val_eq_self value)
  packed.map (digitsEquiv width count) (digitsEquiv width count).symm
    (fun value => (digitsEquiv width count).symm_apply_apply value)

@[simp] theorem encoding_length (width count bytes : Nat)
    (fits : width * count ≤ 8 * bytes) (value : Fin count → BitVec width) :
    ((encoding width count bytes fits).encode value).length = bytes := by
  simp [encoding, Encoding.map]

def curveRows : Encoding (Fin 1270 → BitVec 254) :=
  encoding 254 1270 40323 (by decide)

@[simp] theorem curveRows_length (value : Fin 1270 → BitVec 254) :
    (curveRows.encode value).length = 40323 :=
  encoding_length 254 1270 40323 _ value

end Kriterion.BitRowPacking
