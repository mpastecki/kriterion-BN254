import BN254
import Encoding
import Mathlib.Algebra.BigOperators.Fin

namespace Kriterion.ArgoMAC.FieldPacking

open BN254

/-- Explicit radix-p conversion. Both directions are computable. -/
def digitsEquiv (count : Nat) : (Fin count → BaseField) ≃ Fin (baseFieldModulus ^ count) :=
  (Equiv.piCongrRight fun _ => (ZMod.finEquiv baseFieldModulus).toEquiv.symm).trans
    finFunctionFinEquiv

def byteSplit (remaining : Nat) :
    Fin (256 ^ (remaining + 1)) ≃ Fin 256 × Fin (256 ^ remaining) :=
  (finCongr (pow_succ' 256 remaining)).trans finProdFinEquiv.symm

/-- Put the most significant byte first and retain a fixed total width. -/
def highFirst (remaining : Nat) : Encoding (Fin (256 ^ (remaining + 1))) :=
  (Encoding.byte.pair (Encoding.natural remaining)).map
    (byteSplit remaining) (byteSplit remaining).symm
    (fun value => (byteSplit remaining).symm_apply_apply value)

def narrow (count remaining : Nat)
    (fits : baseFieldModulus ^ count ≤ 256 ^ (remaining + 1)) :
    Encoding (Fin (baseFieldModulus ^ count)) :=
  (highFirst remaining).map
    (fun value => value.castLE fits)
    (fun value => Fin.ofNat (baseFieldModulus ^ count) value.val)
    (fun value => Fin.ofNat_val_eq_self value)

def fields (count remaining : Nat)
    (fits : baseFieldModulus ^ count ≤ 256 ^ (remaining + 1)) :
    Encoding (Fin count → BaseField) :=
  (narrow count remaining fits).map (digitsEquiv count) (digitsEquiv count).symm
    (fun value => (digitsEquiv count).symm_apply_apply value)

@[simp] theorem highFirst_length (remaining : Nat) (value : Fin (256 ^ (remaining + 1))) :
    ((highFirst remaining).encode value).length = remaining + 1 := by
  simp [highFirst, Encoding.map, Encoding.pair, Encoding.byte, Nat.add_comm]

@[simp] theorem fields_length (count remaining : Nat)
    (fits : baseFieldModulus ^ count ≤ 256 ^ (remaining + 1)) (value : Fin count → BaseField) :
    ((fields count remaining fits).encode value).length = remaining + 1 := by
  simp [fields, narrow, Encoding.map]

theorem highFirst_prefix (remaining : Nat) (value : Fin (256 ^ (remaining + 1))) :
    ∃ tail, (highFirst remaining).encode value = (byteSplit remaining value).1 :: tail := by
  exact ⟨(Encoding.natural remaining).encode (byteSplit remaining value).2, rfl⟩

theorem byteSplit_ne_255 (remaining : Nat) (value : Fin (256 ^ (remaining + 1)))
    (bound : value.val < 255 * 256 ^ remaining) : (byteSplit remaining value).1 ≠ 255 := by
  intro equal
  have same := congrArg Fin.val equal
  change value.val / 256 ^ remaining = 255 at same
  have less : value.val / 256 ^ remaining < 255 :=
    (Nat.div_lt_iff_lt_mul (by positivity)).mpr bound
  omega

/-- The unused leading-byte range supplies a disjoint generic fallback marker. -/
theorem fields_prefix (count remaining : Nat)
    (fits : baseFieldModulus ^ count ≤ 256 ^ (remaining + 1))
    (room : baseFieldModulus ^ count ≤ 255 * 256 ^ remaining) (value : Fin count → BaseField) :
    ∃ first tail, (fields count remaining fits).encode value = first :: tail ∧ first ≠ 255 := by
  let packed := (digitsEquiv count value).castLE fits
  obtain ⟨tail, leading⟩ := highFirst_prefix remaining packed
  refine ⟨(byteSplit remaining packed).1, tail, leading, ?_⟩
  apply byteSplit_ne_255
  exact lt_of_lt_of_le (digitsEquiv count value).isLt room

/-- Fourteen coefficients fit in 444 bytes instead of 448 bytes. -/
def fourteen : Encoding (Fin 14 → BaseField) := fields 14 443 (by decide)

@[simp] theorem fourteen_length (value : Fin 14 → BaseField) :
    (fourteen.encode value).length = 444 := fields_length 14 443 _ value

theorem fourteen_prefix (value : Fin 14 → BaseField) :
    ∃ first tail, fourteen.encode value = first :: tail ∧ first ≠ 255 :=
  fields_prefix 14 443 _ (by decide) value

end Kriterion.ArgoMAC.FieldPacking
