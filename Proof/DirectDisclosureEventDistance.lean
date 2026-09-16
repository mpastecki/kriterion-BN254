import Cryptography.Probability
import Mathlib.Tactic.Linarith

namespace Kriterion.DirectDisclosure.EventDistance

open scoped ENNReal
noncomputable section

private def mass {A : Type*} (p : PMF A) (event : Set A) : ℝ :=
  (p.toOuterMeasure event).toReal

private theorem finite_mass {A : Type*} (p : PMF A) (event : Set A) :
    p.toOuterMeasure event ≠ ⊤ := by
  rw [← Cryptography.Probability.event_eq]
  exact probEvent_ne_top

private theorem mass_le_one {A : Type*} (p : PMF A) (event : Set A) : mass p event ≤ 1 := by
  have bounded : p.toOuterMeasure event ≤ 1 := by
    rw [← Cryptography.Probability.event_eq]
    exact probEvent_le_one
  exact (ENNReal.toReal_mono ENNReal.one_ne_top bounded).trans_eq (by simp)

private theorem mass_partition {A : Type*} (p : PMF A) (event : Set A) :
    mass p event + mass p eventᶜ = 1 := by
  have total := probEvent_compl p (fun x => x ∈ event)
  simp only [probFailure_eq_zero, tsub_zero] at total
  change probEvent p event + probEvent p eventᶜ = 1 at total
  erw [Cryptography.Probability.event_eq, Cryptography.Probability.event_eq] at total
  have real := congrArg ENNReal.toReal total
  erw [ENNReal.toReal_add (finite_mass p event) (finite_mass p eventᶜ),
    ENNReal.toReal_one] at real
  exact real

def good {A : Type*} (event : Set A) : Set (A × Bool) :=
  {pair | pair.1 ∈ event ∧ pair.2 = false}

def bad {A : Type*} : Set (A × Bool) := {pair | pair.2 = true}

private theorem projected_le_good_bad {A : Type*} (flagged : PMF (A × Bool)) (event : Set A) :
    mass (flagged.map Prod.fst) event ≤ mass flagged (good event) + mass flagged bad := by
  have cover : Prod.fst ⁻¹' event ⊆ good event ∪ bad := by
    rintro ⟨value, flag⟩ member
    cases flag with
    | false => exact Or.inl ⟨member, rfl⟩
    | true => exact Or.inr rfl
  have bound : flagged.toOuterMeasure (Prod.fst ⁻¹' event) ≤
      flagged.toOuterMeasure (good event) + flagged.toOuterMeasure bad :=
    (MeasureTheory.measure_mono cover).trans (MeasureTheory.measure_union_le _ _)
  have real := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨finite_mass flagged _, finite_mass flagged _⟩) bound
  rw [ENNReal.toReal_add (finite_mass flagged _) (finite_mass flagged _)] at real
  simpa only [mass, PMF.toOuterMeasure_map_apply] using real

/-- A one-sided lower bound on good flagged mass yields a two-sided event bound.
This lemma does not assert that any cryptographic game satisfies its hypotheses. -/
theorem flagged_event_distance {A : Type*} (real ideal : PMF A) (flagged : PMF (A × Bool))
    (epsilon beta delta : ℝ) (epsilon_nonnegative : 0 ≤ epsilon)
    (good_bound : ∀ event : Set A,
      (1 - epsilon) * (flagged.toOuterMeasure (good event)).toReal ≤
        (real.toOuterMeasure event).toReal)
    (bad_bound : (flagged.toOuterMeasure bad).toReal ≤ beta)
    (transport : ∀ event : Set A,
      |((flagged.map Prod.fst).toOuterMeasure event).toReal - (ideal.toOuterMeasure event).toReal| ≤ delta)
    (event : Set A) :
    |(real.toOuterMeasure event).toReal - (ideal.toOuterMeasure event).toReal| ≤ epsilon + beta + delta := by
  have one_sided (set : Set A) :
      mass (flagged.map Prod.fst) set ≤ mass real set + epsilon + beta := by
    have split := projected_le_good_bad flagged set
    have scaled := mul_le_mul_of_nonneg_left (mass_le_one flagged (good set)) epsilon_nonnegative
    have lower := good_bound set
    change (1 - epsilon) * mass flagged (good set) ≤ mass real set at lower
    change mass flagged bad ≤ beta at bad_bound
    nlinarith
  have distance : |mass real event - mass (flagged.map Prod.fst) event| ≤ epsilon + beta := by
    rw [abs_le]
    constructor
    · linarith [one_sided event]
    · linarith [one_sided eventᶜ, mass_partition real event,
        mass_partition (flagged.map Prod.fst) event]
  have second := transport event
  change |mass (flagged.map Prod.fst) event - mass ideal event| ≤ delta at second
  change |mass real event - mass ideal event| ≤ _
  calc
    _ = |(mass real event - mass (flagged.map Prod.fst) event) +
        (mass (flagged.map Prod.fst) event - mass ideal event)| := by congr 1; ring
    _ ≤ |mass real event - mass (flagged.map Prod.fst) event| +
        |mass (flagged.map Prod.fst) event - mass ideal event| := abs_add_le _ _
    _ ≤ (epsilon + beta) + delta := add_le_add distance second

end
end Kriterion.DirectDisclosure.EventDistance
