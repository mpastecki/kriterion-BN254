import Proof.DirectDisclosureFullSource
import Proof.ConditionalDisclosureKeyRatio
import Proof.Privacy.Source.TagFiberMass

namespace Kriterion.ConditionalDisclosure.CurveSource

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

def tagMass [Fintype Block] (bridge mask r1 r2 : BaseField)
    (reference : Garbling.Randomness) (input : AffineInput) (mac : InputMac)
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) (tag : FullSource) : ℝ≥0∞ :=
  (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
    {sample | sample.2.encodeAffine input = mac ∧ actual bridge mask r1 r2 sample.1 sample.2 = tag ∧
      OracleTranscriptCompatible Garbling.oracleHandler {reference with fixedKeyOracle := sample.1} transcript}

def publicMass [Fintype Block] (bridge mask r1 r2 : BaseField)
    (reference : Garbling.Randomness) (input : AffineInput) (mac : InputMac)
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) (publicTable : CurveMembership.Table) : ℝ≥0∞ :=
  (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
    {sample | CurveMembership.garble bridge mask r1 r2 (Pipeline.curveOracles sample.1) sample.2 = publicTable ∧
      sample.2.encodeAffine input = mac ∧
      OracleTranscriptCompatible Garbling.oracleHandler {reference with fixedKeyOracle := sample.1} transcript}

/-- Complete full-tag fibers with the observed table sum below the actual real
public/selected-label/full-transcript event. No source independence is assumed. -/
theorem complete_tag_sum_le [Fintype Block] (bridge mask r1 r2 : BaseField)
    (reference : Garbling.Randomness) (input : AffineInput) (mac : InputMac)
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) (publicTable : CurveMembership.Table) :
    (∑' tag : FullSource, if Complete tag.1 ∧ sourceTable bridge mask (decodeTag r1 r2 tag) = publicTable
      then tagMass bridge mask r1 r2 reference input mac transcript tag else 0) ≤
      publicMass bridge mask r1 r2 reference input mac transcript publicTable := by
  let samples := PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)
  let tagMap := fun sample : (PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey =>
    actual bridge mask r1 r2 sample.1 sample.2
  let event := fun sample : (PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey =>
    CurveMembership.garble bridge mask r1 r2 (Pipeline.curveOracles sample.1) sample.2 = publicTable ∧
    sample.2.encodeAffine input = mac ∧
    OracleTranscriptCompatible Garbling.oracleHandler {reference with fixedKeyOracle := sample.1} transcript
  let kept := fun tag : FullSource =>
    Complete tag.1 ∧ sourceTable bridge mask (decodeTag r1 r2 tag) = publicTable
  refine le_trans (ENNReal.tsum_le_tsum fun tag => ?_)
    (tagFiberMass_restricted_le samples tagMap event kept)
  by_cases retain : kept tag
  · rw [if_pos retain, if_pos retain]
    apply MeasureTheory.measure_mono
    intro sample member
    exact ⟨member.2.1,
      (actual_tag_table bridge mask r1 r2 tag retain.1 sample.1 sample.2 member.2.1).trans retain.2,
      member.1, member.2.2⟩
  · rw [if_neg retain, if_neg retain]

end
end Kriterion.ConditionalDisclosure.CurveSource
