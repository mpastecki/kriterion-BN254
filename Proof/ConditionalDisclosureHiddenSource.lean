import Proof.ConditionalDisclosureAdaptiveSource
import Proof.Privacy.Distribution.AdaptiveOffCurveDistribution
import Proof.Privacy.Collision.HiddenLinkBad

namespace Kriterion.ConditionalDisclosure.HiddenSource

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The choice may retain the full public sample, ciphertext, and prefix transcript.
Only invalid inputs contribute to this comparison. -/
def retained [FieldCertificate] {Aux Observation : Type*}
    (sample : (AffineInput × Aux) → CurvePublicSample)
    (observe : (AffineInput × Aux) → BaseField → BaseField → CurveMaskSample → PMF Observation)
    (choice : AffineInput × Aux) (bridge mask : BaseField) : PMF (Option Observation) :=
  if OnCurve choice.1 then PMF.pure none else
    (observe choice bridge mask (curveMaskSampleSplit bridge mask choice.1 (sample choice)).2).map some

/-- The actual nonzero mask is recovered from the hidden bridge and chosen result. -/
def reindexed [FieldCertificate] {Aux Observation : Type*}
    (sample : (AffineInput × Aux) → CurvePublicSample)
    (observe : (AffineInput × Aux) → BaseField → BaseField → CurveMaskSample → PMF Observation)
    (choice : AffineInput × Aux) (bridge target : BaseField) : PMF (Option Observation) :=
  retained sample observe choice bridge
    ((target - bridge) / (choice.1.x ^ 3 + 3 - choice.1.y ^ 2))

theorem reindexed_actual [FieldCertificate] {Aux Observation : Type*}
    (sample : (AffineInput × Aux) → CurvePublicSample)
    (observe : (AffineInput × Aux) → BaseField → BaseField → CurveMaskSample → PMF Observation)
    (choice : AffineInput × Aux) (bridge mask : BaseField) :
    reindexed sample observe choice bridge
      (bridge + mask * (choice.1.x ^ 3 + 3 - choice.1.y ^ 2)) =
    retained sample observe choice bridge mask := by
  by_cases valid : OnCurve choice.1
  · simp only [reindexed, retained, if_pos valid]
  · unfold reindexed
    rw [add_sub_cancel_left, mul_div_cancel_right₀ _ (curveResidual_ne_zero choice.1 valid)]

private theorem selected_result [FieldCertificate] {Aux Observation : Type*}
    (sample : (AffineInput × Aux) → CurvePublicSample)
    (observe : (AffineInput × Aux) → BaseField → BaseField → CurveMaskSample → PMF Observation)
    (choice : AffineInput × Aux) (pair : BaseField × BaseField) :
    reindexed sample observe choice pair.1 (selectedCurveIdealResult choice.1 pair) =
      reindexed sample observe choice pair.1 pair.2 := by
  by_cases valid : OnCurve choice.1
  · simp only [reindexed, retained, if_pos valid]
  · simp only [selectedCurveIdealResult, if_neg valid]

/-- For an independent hidden bridge/mask pair, the exact law retains every original
curve source field after an arbitrary public-dependent input choice. -/
theorem full_mask_transport [FieldCertificate] {Aux Observation : Type*}
    (selected : PMF (AffineInput × Aux))
    (sample : (AffineInput × Aux) → CurvePublicSample)
    (observe : (AffineInput × Aux) → BaseField → BaseField → CurveMaskSample → PMF Observation) :
    (selected.bind fun choice =>
      (PMF.uniformOfFintype (BaseField × BaseField)).bind fun pair =>
        retained sample observe choice pair.1 pair.2) =
    (selected.bind fun choice =>
      (PMF.uniformOfFintype (BaseField × BaseField)).bind fun pair =>
        reindexed sample observe choice pair.1 pair.2) := by
  have law := adaptiveCurveKey_uniform selected (reindexed sample observe)
  simp only [reindexed_actual, selected_result] at law
  exact law

/-- Restricting the actual mask to nonzero loses at most one field inverse for the
complete observation, including retained prefix state and source prescriptions. -/
theorem nonzero_mask_observation_bound [FieldCertificate] {Aux Observation : Type*}
    (selected : PMF (AffineInput × Aux))
    (sample : (AffineInput × Aux) → CurvePublicSample)
    (observe : (AffineInput × Aux) → BaseField → BaseField → CurveMaskSample → PMF Observation)
    (event : Set (Option Observation)) :
    |((selected.bind fun choice =>
        (PMF.uniformOfFintype (BaseField × BaseField)).bind fun pair =>
          reindexed sample observe choice pair.1 pair.2).toOuterMeasure event).toReal -
      ((selected.bind fun choice =>
        (PMF.uniformOfFintype BaseField).bind fun bridge =>
          (PMF.uniformOfFintype NonZeroBase).bind fun mask =>
            retained sample observe choice bridge mask.value).toOuterMeasure event).toReal| ≤
      1 / (baseFieldModulus : ℝ) := by
  have bound := adaptiveCurveMask_observation_bound selected (reindexed sample observe) event
  simp only [reindexed_actual, selected_result] at bound
  exact bound

/-- This source-independent hidden bridge excludes the zero-mask diagonal and
all actually retained hash queries; the ciphertext remains part of Source. -/
theorem hidden_hash_bad_mass {Source : Type*} (samples : PMF Source)
    (target : Source → BaseField)
    (transcript : Source → List (Sigma Garbling.oracleSpec.Answer)) (budget : Nat)
    (bounded : ∀ source ∈ samples.support, (transcript source).length ≤ budget) :
    (samples.bind fun source => (PMF.uniformOfFintype BaseField).map (Prod.mk source)).toOuterMeasure
      {pair | pair.2 = target pair.1 ∨ pair.2 ∈ transcriptHashInputs (transcript pair.1)} ≤
        (1 + budget : ℝ≥0∞) / baseFieldModulus :=
  hiddenLinkBad_source_mass_le samples target transcript budget bounded

end
end Kriterion.ConditionalDisclosure.HiddenSource
