import Proof.ConditionalDisclosureHashSource
import Proof.Privacy.Bounds.AdaptiveArithmetic

namespace Kriterion.DirectDisclosure

open BN254 ArgoMAC.Security

/-- The direct-disclosure arithmetic envelope is bounded by a uniform 128-bit term. -/
theorem numeric_error_bound (qBefore q : Nat) (bounded : qBefore ≤ q) :
    (2 * (q : ℝ) / (2 : ℝ) ^ 128) +
      (12700 * (qBefore : ℝ) / (2 : ℝ) ^ 128) +
      2 / (baseFieldModulus : ℝ) +
      2 * (1270 * (2 ^ 384 % baseFieldModulus : Nat) / (2 : ℝ) ^ 384) ≤
        32768 * ((q : ℝ) + 1) / (2 : ℝ) ^ 128 := by
  have field : (1 : ℝ) / baseFieldModulus ≤ 1 / (2 : ℝ) ^ 128 :=
    fieldMaskLoss_le_block
  have rounding : (1270 : ℝ) * (2 ^ 384 % baseFieldModulus : Nat) / (2 : ℝ) ^ 384 ≤
      1270 / (2 : ℝ) ^ 128 :=
    ConditionalDisclosure.CurveSource.hash_rounding_le_blocks
  have before : (qBefore : ℝ) ≤ q := by exact_mod_cast bounded
  have positive : 0 < (2 : ℝ) ^ 128 := by positivity
  have fieldTwo : 2 / (baseFieldModulus : ℝ) ≤ 2 / (2 : ℝ) ^ 128 := by
    calc
      2 / (baseFieldModulus : ℝ) = 2 * ((1 : ℝ) / baseFieldModulus) := by ring
      _ ≤ 2 * (1 / (2 : ℝ) ^ 128) :=
        mul_le_mul_of_nonneg_left field (by norm_num)
      _ = 2 / (2 : ℝ) ^ 128 := by ring
  calc
    _ ≤ 2 * (q : ℝ) / (2 : ℝ) ^ 128 +
        12700 * (qBefore : ℝ) / (2 : ℝ) ^ 128 +
        2 / (2 : ℝ) ^ 128 + 2 * (1270 / (2 : ℝ) ^ 128) := by
          nlinarith [fieldTwo, rounding]
    _ = (2 * (q : ℝ) + 12700 * (qBefore : ℝ) + 2542) / (2 : ℝ) ^ 128 := by ring
    _ ≤ 32768 * ((q : ℝ) + 1) / (2 : ℝ) ^ 128 := by
      have numerator : 2 * (q : ℝ) + 12700 * (qBefore : ℝ) + 2542 ≤
          32768 * ((q : ℝ) + 1) := by nlinarith
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_right numerator (by positivity : 0 ≤ ((2 : ℝ) ^ 128)⁻¹)

theorem numeric_security_bound (qBefore q : Nat) (bounded : qBefore ≤ q) :
    32768 * ((q : ℝ) + 1) / (2 : ℝ) ^ 128 ≤
      ((q : ℝ) + 1) / (2 : ℝ) ^ 100 := by
  have positive : 0 < (2 : ℝ) ^ 128 := by positivity
  norm_num [div_eq_mul_inv]
  ring_nf
  nlinarith

/-- Multiplying the concrete envelope by the fixed 100-bit factor costs at most `q + 1`. -/
theorem numeric_work_bound (qBefore q : Nat) (bounded : qBefore ≤ q) :
    ((2 * (q : ℝ) / (2 : ℝ) ^ 128) +
      (12700 * (qBefore : ℝ) / (2 : ℝ) ^ 128) +
      2 / (baseFieldModulus : ℝ) +
      2 * (1270 * (2 ^ 384 % baseFieldModulus : Nat) / (2 : ℝ) ^ 384)) *
        (2 : ℝ) ^ 100 ≤ (q : ℝ) + 1 := by
  have error := numeric_error_bound qBefore q bounded
  have factor : 32768 * (2 : ℝ) ^ 100 / (2 : ℝ) ^ 128 ≤ 1 := by
    norm_num [div_eq_mul_inv]
  have qNonnegative : 0 ≤ (q : ℝ) + 1 := by positivity
  calc
    _ ≤ (32768 * ((q : ℝ) + 1) / (2 : ℝ) ^ 128) * (2 : ℝ) ^ 100 :=
      mul_le_mul_of_nonneg_right error (by positivity)
    _ = ((q : ℝ) + 1) * (32768 * (2 : ℝ) ^ 100 / (2 : ℝ) ^ 128) := by ring
    _ ≤ (q : ℝ) + 1 := by nlinarith

theorem query_term_nonnegative_and_le_one (q : Nat) (small : q < 2 ^ 100) :
    0 ≤ 2 * (q : ℝ) / (2 : ℝ) ^ 128 ∧
      2 * (q : ℝ) / (2 : ℝ) ^ 128 ≤ 1 := by
  constructor
  · positivity
  · have bound : (q : ℝ) < (2 : ℝ) ^ 100 := by exact_mod_cast small
    have positive : 0 < (2 : ℝ) ^ 128 := by positivity
    nlinarith [show (2 : ℝ) ^ 100 * 2 ≤ (2 : ℝ) ^ 128 by norm_num]

end Kriterion.DirectDisclosure
