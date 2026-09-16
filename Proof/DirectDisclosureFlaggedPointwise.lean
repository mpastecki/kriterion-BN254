import Proof.DirectDisclosureEventDistance

namespace Kriterion.DirectDisclosure.EventDistance
open scoped ENNReal
noncomputable section

/-- The good event keeps exactly the false-flag fiber of each selected transcript. -/
theorem good_mass_eq {A : Type*} (flagged : PMF (A × Bool)) (event : Set A) :
    flagged.toOuterMeasure (good event) = ∑' a, event.indicator (fun a => flagged (a, false)) a := by
  classical
  rw [PMF.toOuterMeasure_apply, ENNReal.tsum_prod']
  apply tsum_congr
  intro a
  simp [good, Set.indicator]

/-- A pointwise nonnegative source factor bounds every complete good event. -/
theorem pointwise_good_event {A : Type*} (real : PMF A) (flagged : PMF (A × Bool))
    (factor : ℝ≥0∞) (pointwise : ∀ a, factor * flagged (a, false) ≤ real a) (event : Set A) :
    factor * flagged.toOuterMeasure (good event) ≤ real.toOuterMeasure event := by
  classical
  rw [good_mass_eq, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro a
  by_cases member : a ∈ event
  · simpa only [Set.indicator_of_mem member] using pointwise a
  · simp only [Set.indicator_of_notMem member, mul_zero, le_refl]

/-- Convert the nonnegative extended-real ratio to the real event premise used by
`flagged_event_distance`. No claim about a particular source is introduced. -/
theorem pointwise_good_event_real {A : Type*} (real : PMF A) (flagged : PMF (A × Bool))
    (loss : ℝ≥0∞) (small : loss ≤ 1)
    (pointwise : ∀ a, (1 - loss) * flagged (a, false) ≤ real a) (event : Set A) :
    (1 - loss.toReal) * (flagged.toOuterMeasure (good event)).toReal ≤
      (real.toOuterMeasure event).toReal := by
  have finite : real.toOuterMeasure event ≠ ⊤ := by
    rw [← Cryptography.Probability.event_eq]
    exact probEvent_ne_top
  have bound := ENNReal.toReal_mono finite (pointwise_good_event real flagged (1-loss) pointwise event)
  rw [ENNReal.toReal_mul, ENNReal.toReal_sub_of_le small ENNReal.one_ne_top, ENNReal.toReal_one] at bound
  exact bound

end
end Kriterion.DirectDisclosure.EventDistance
