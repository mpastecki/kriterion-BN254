import Proof.DirectDisclosureTagDomination

namespace Kriterion.DirectDisclosure.SourceKernel

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype bitAdaptorTableFintype transcriptOracleFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
local instance : Nonempty FullTag := ⟨(fun _ => 0, fun _ => defaultBitAdaptorTable)⟩

private theorem weighted_zero (loss weight target : ℝ≥0∞) : loss * (weight * 0) ≤ target := by
  rw [mul_zero, mul_zero]
  exact bot_le

/-- Static guards, incompatible nonfixed replies, and bad prefix grids are handled
without adding premises to the complete retained-tag comparison. -/
theorem retained_tag_le {Aux : Type}
    (scalar : ScalarField) (rest : GarblingSourceRest) (tag : FullTag) (publicTable : Public)
    (selected : AffineInput × Aux) (labels : Garbling.Labels) (reference : SimulatorState)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible idealOracleHandler reference before)
    (queries : Nat) (small : queries < 2 ^ 100) (bounded : (before ++ after).length ≤ queries) :
    (1 - (2 * (before ++ after).length : Nat) / (Fintype.card Block : ℝ≥0∞)) *
      ((PMF.uniformOfFintype FullTag) tag * (PMF.uniformOfFintype OracleKey).toOuterMeasure
        {sample | retainedGoodEvent scalar rest tag publicTable selected labels before after sample}) ≤
      if ConditionalDisclosure.CurveSource.Complete tag.1 ∧ retainedTable scalar rest tag = publicTable then
        ConditionalDisclosure.CurveSource.tagMass (embedScalar scalar) rest.algebraic.field.curveMask.value
          rest.algebraic.field.curveR1 rest.algebraic.field.curveR2 rest.reference selected.1 labels.inputMac
          (before ++ after) tag else 0 := by
  by_cases kept : ConditionalDisclosure.CurveSource.Complete tag.1 ∧ retainedTable scalar rest tag = publicTable
  · rw [if_pos kept]
    by_cases bits : BitInput.ofAffine selected.1 = labels.input
    · by_cases nonfixed : NonFixedTranscriptCompatible rest.reference (before ++ after)
      · by_cases good : ¬ LabelCollision.GridCollision (retainedPrefix reference rest before).fixedTranscript
          (LabelCollision.selectedUses (retainedRequest scalar rest tag selected.1) selected.1)
          (selectedPublicKey selected.1 (inputMacCoordinateEquiv labels.inputMac))
        · rw [retained_good_mass_guard, if_pos ⟨kept.1, kept.2, bits⟩]
          exact retained_good_tag_le scalar rest tag kept.1 selected.1 labels.inputMac reference before after
            compatible nonfixed good queries small bounded
        · have initialCompatible := sourcePrefixReference_compatible reference rest before compatible
            ((nonFixedTranscriptCompatible_append rest.reference before after).mp nonfixed).1
          letI : Nonempty (TranscriptOracle
              (transcriptFinalState idealOracleHandler (pairInitial rest reference.fixedOracle) before).fixedTranscript) := by
            change Nonempty (TranscriptOracle (retainedPrefix reference rest before).fixedTranscript)
            exact sourcePrefixReference_oracleExists reference rest before compatible
          have normalized := retained_joint_mass scalar rest tag selected.1 labels.inputMac reference.fixedOracle before after initialCompatible
          have bad : ¬ (¬ LabelCollision.GridCollision
              (transcriptFinalState idealOracleHandler (pairInitial rest reference.fixedOracle) before).fixedTranscript
              (LabelCollision.selectedUses (retainedRequest scalar rest tag selected.1) selected.1)
              (selectedPublicKey selected.1 (inputMacCoordinateEquiv labels.inputMac))) := good
          rw [if_neg bad] at normalized
          rw [retained_good_mass_guard, if_pos ⟨kept.1, kept.2, bits⟩, normalized]
          exact weighted_zero _ _ _
      · rw [retainedGoodEvent_mass_zero scalar rest tag publicTable selected labels before after nonfixed]
        exact weighted_zero _ _ _
    · have rejected : ¬ (ConditionalDisclosure.CurveSource.Complete tag.1 ∧ retainedTable scalar rest tag = publicTable ∧
          BitInput.ofAffine selected.1 = labels.input) := fun h => bits h.2.2
      rw [retained_good_mass_guard, if_neg rejected]
      exact weighted_zero _ _ _
  · have rejected : ¬ (ConditionalDisclosure.CurveSource.Complete tag.1 ∧ retainedTable scalar rest tag = publicTable ∧
        BitInput.ofAffine selected.1 = labels.input) := fun h => kept ⟨h.1, h.2.1⟩
    rw [retained_good_mass_guard, if_neg rejected, if_neg kept]
    exact weighted_zero _ _ _

/-- Summing every complete retained tag gives the actual real public/MAC/full-query
source event, with the same two-query-per-hidden-label loss. -/
theorem retained_source_sum_le {Aux : Type}
    (scalar : ScalarField) (rest : GarblingSourceRest) (publicTable : Public)
    (selected : AffineInput × Aux) (labels : Garbling.Labels) (reference : SimulatorState)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible idealOracleHandler reference before)
    (queries : Nat) (small : queries < 2 ^ 100) (bounded : (before ++ after).length ≤ queries) :
    (1 - (2 * (before ++ after).length : Nat) / (Fintype.card Block : ℝ≥0∞)) *
      (∑' tag : FullTag, (PMF.uniformOfFintype FullTag) tag * (PMF.uniformOfFintype OracleKey).toOuterMeasure
        {sample | retainedGoodEvent scalar rest tag publicTable selected labels before after sample}) ≤
      Endpoint.retainedPublicMass scalar rest publicTable selected.1 labels.inputMac (before ++ after) := by
  rw [← ENNReal.tsum_mul_left]
  apply le_trans (ENNReal.tsum_le_tsum fun tag =>
    retained_tag_le scalar rest tag publicTable selected labels reference before after compatible queries small bounded)
  exact ConditionalDisclosure.CurveSource.complete_tag_sum_le (embedScalar scalar)
    rest.algebraic.field.curveMask.value rest.algebraic.field.curveR1 rest.algebraic.field.curveR2
    rest.reference selected.1 labels.inputMac (before ++ after) publicTable

end
end Kriterion.DirectDisclosure.SourceKernel
