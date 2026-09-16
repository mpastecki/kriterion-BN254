import Proof.ConditionalDisclosureCurve
import Proof.Privacy.Collision.CircuitSlotRatio

namespace Kriterion.ConditionalDisclosure.CurveSource

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] rawBucketUseFintype rawInactiveBucketFintype fixedQueryDomainFintype residualFixedQueryDomainFintype

/-- A curve bucket has at most one source assignment, even before any labels are fixed. -/
theorem bucket_card_le_one (source : CurveMaskSample) (inputKey : InputMacKey)
    (lifts : Gate → FullHashLift) (index : Pipeline.FixedKeyIndex) :
    Fintype.card (RawBucketUse (prescription source inputKey lifts) index) ≤ 1 := by
  letI := bucket_subsingleton source inputKey lifts index
  have bounded := Fintype.card_le_of_injective
    (fun _ : RawBucketUse (prescription source inputKey lifts) index => Unit.unit)
    (fun _ _ _ => Subsingleton.elim _ _)
  simpa using bounded

/-- The source has no repeated tweak or range within any physical permutation bucket. -/
theorem bucket_assignments_injective (source : CurveMaskSample) (inputKey : InputMacKey)
    (lifts : Gate → FullHashLift) (index : Pipeline.FixedKeyIndex) :
    Function.Injective (rawBucketTweak (prescription source inputKey lifts) index) ∧
      Function.Injective (rawBucketOffset (prescription source inputKey lifts) index) := by
  letI := bucket_subsingleton source inputKey lifts index
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ _ _ => Subsingleton.elim _ _⟩

/-- Each external query excludes at most two hidden labels across the actual curve source. -/
theorem inactive_loss_le [Fintype Block] (source : CurveMaskSample) (inputKey : InputMacKey)
    (lifts : Gate → FullHashLift) (selected : RawLabelBucket → Bool)
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) :
    (∑ index : RawInactiveBucket selected,
      ((2 * Fintype.card (RawBucketUse (prescription source inputKey lifts) index.1) *
        Fintype.card (FixedQueryDomain (fixedOracleTranscriptRecords transcript) index.1) : Nat) : ℝ≥0∞) /
          Fintype.card Block) ≤ (2 * transcript.length : Nat) / (Fintype.card Block : ℝ≥0∞) := by
  classical
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  apply mul_le_mul_left
  simp only [← Nat.cast_sum]
  apply Nat.cast_le.mpr
  calc
    _ ≤ ∑ index : RawInactiveBucket selected,
        2 * Fintype.card (FixedQueryDomain (fixedOracleTranscriptRecords transcript) index.1) := by
      apply Finset.sum_le_sum
      intro index _
      have uses := bucket_card_le_one source inputKey lifts index.1
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 uses)
    _ ≤ ∑ index : Pipeline.FixedKeyIndex,
        2 * Fintype.card (FixedQueryDomain (fixedOracleTranscriptRecords transcript) index) :=
      (Nat.le_add_right _ _).trans_eq (Fintype.sum_subtype_add_sum_subtype
        (fun index => rawSlotBranch index.slot ≠ selected (rawLabelBucket index))
        (fun index => 2 * Fintype.card
          (FixedQueryDomain (fixedOracleTranscriptRecords transcript) index)))
    _ = 2 * ∑ index : Pipeline.FixedKeyIndex,
        Fintype.card (FixedQueryDomain (fixedOracleTranscriptRecords transcript) index) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * transcript.length := Nat.mul_le_mul_left _ (fixedExternalQueryCount_le transcript)

/-- This conditional source count retains legal repeated queries at active programmed
points through the exact residual query domains. It is not an iid marginal argument. -/
theorem inactive_realTranscript_mass_ge {Wire : Type} [Fintype Wire] [DecidableEq Wire]
    [Fintype Block]
    (source : CurveMaskSample) (inputKey : InputMacKey) (lifts : Gate → FullHashLift)
    (selected : RawLabelBucket → Bool) (wire : RawLabelBucket → Wire)
    (shift : RawLabelBucket → Block) (publicLabel : RawLabelBucket → Block)
    (randomness : Garbling.Randomness) (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible Garbling.oracleHandler randomness transcript)
    (referenceActive : ∀ index, rawSlotBranch index.slot = selected (rawLabelBucket index) →
      ∀ use : RawBucketUse (prescription source inputKey lifts) index,
        randomness.fixedKeyOracle.permutation index
          (publicLabel (rawLabelBucket index) ^^^
            rawBucketTweak (prescription source inputKey lifts) index use) =
          rawBucketOffset (prescription source inputKey lifts) index use ^^^ publicLabel (rawLabelBucket index)) :
    (1 - (2 * transcript.length : Nat) / (Fintype.card Block : ℝ≥0∞)) *
      (∏ index, ((Fintype.card Block -
        (Fintype.card (RawBucketUse (prescription source inputKey lifts) index) +
          Fintype.card (ResidualFixedQueryDomain (fixedOracleTranscriptRecords transcript)
            (rawActiveDomains (prescription source inputKey lifts) selected publicLabel) index))).factorial :
              ℝ≥0∞) / (Fintype.card Block).factorial) ≤
    (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × (Wire → Block))).toOuterMeasure
      {sample | RawGarblingMatches
        (rawGatesWithLabels (prescription source inputKey lifts)
          (rawMixedLabels selected publicLabel wire shift sample.2)) sample.1 ∧
        OracleTranscriptCompatible Garbling.oracleHandler
          {randomness with fixedKeyOracle := sample.1} transcript} := by
  have mass := rawSharedInactive_realTranscript_mass_ge
    (prescription source inputKey lifts) selected wire shift publicLabel randomness transcript compatible
    (fun index => (bucket_assignments_injective source inputKey lifts index).1)
    (fun index => (bucket_assignments_injective source inputKey lifts index).2) referenceActive
  apply le_trans _ mass
  apply mul_le_mul'
  · exact tsub_le_tsub_left (inactive_loss_le source inputKey lifts selected transcript) 1
  · exact le_rfl

end
end Kriterion.ConditionalDisclosure.CurveSource
