import Proof.ConditionalDisclosureProgramRatio
import Proof.DirectDisclosureSourceSum

namespace Kriterion.ConditionalDisclosure.CurveSource

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] rawBucketUseFintype fixedQueryDomainFintype residualFixedQueryDomainFintype
  transcriptOracleFintype publicInputMacKeyFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- The actual selected-program probability, scaled by its complete source and
visible-label masses, is dominated by the actual real full-tag event. The remaining
premises are the concrete transcript/schedule obligations, not source independence. -/
theorem programmed_tag_mass_le [Fintype Block]
    (bridge mask r1 r2 : BaseField)
    (randomness : Garbling.Randomness)
    (source : CurveMaskSample) (inputKey : InputMacKey) (lifts : Gate → FullHashLift)
    (randomizers : source.1.1 = ![r1, r2])
    (residues : ∀ gate, field source gate = ((lifts gate).val : BaseField))
    (input : AffineInput) (mac : InputMac)
    (state : SimulatorState) (schedule : List GateDirective)
    (queries : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible Garbling.oracleHandler randomness transcript)
    (referenceActive : ∀ index, rawSlotBranch index.slot = circuitBucketInputBit input (rawLabelBucket index) →
      ∀ use : RawBucketUse (prescription source inputKey lifts) index,
        randomness.fixedKeyOracle.permutation index
          (circuitBucketInputLabel mac mac (rawLabelBucket index) ^^^
            rawBucketTweak (prescription source inputKey lifts) index use) =
          rawBucketOffset (prescription source inputKey lifts) index use ^^^
            circuitBucketInputLabel mac mac (rawLabelBucket index))
    (fresh : FreshRecordSchedule state.fixedTranscript (gateProgramRecords schedule))
    [Nonempty (TranscriptOracle state.fixedTranscript)]
    (reference : TranscriptOracle
      (programRecordHistory state.fixedTranscript (gateProgramRecords schedule) ++ queries))
    (recordCounts : ∀ index, Fintype.card (FixedQueryDomain (gateProgramRecords schedule) index) =
      if rawSlotBranch index.slot = circuitBucketInputBit input (rawLabelBucket index)
      then uses source inputKey lifts index else 0)
    (residualCounts : ∀ index,
      Fintype.card (ResidualFixedQueryDomain (state.fixedTranscript ++ queries)
        (programmedDomains (gateProgramRecords schedule)) index) =
      Fintype.card (ResidualFixedQueryDomain (fixedOracleTranscriptRecords transcript)
        (rawActiveDomains (prescription source inputKey lifts) (circuitBucketInputBit input)
          (circuitBucketInputLabel mac mac)) index))
    (priorFits : ∀ index, uses source inputKey lifts index +
      Fintype.card (FixedQueryDomain state.fixedTranscript index) ≤ Fintype.card Block)
    (residualFits : ∀ index, uses source inputKey lifts index +
      Fintype.card (ResidualFixedQueryDomain (state.fixedTranscript ++ queries)
        (programmedDomains (gateProgramRecords schedule)) index) ≤ Fintype.card Block) :
    (1 - (2 * transcript.length : Nat) / (Fintype.card Block : ℝ≥0∞)) *
      ((Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
        (sourceFactor source inputKey lifts * fixedTranscriptFactor state.fixedTranscript *
          ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map (fun oracle =>
            programGateSchedule {state with fixedOracle := oracle.1} schedule)).toOuterMeasure
              {programmed | PermutationTranscriptMatches programmed.fixedOracle queries})) ≤
      tagMass bridge mask r1 r2 randomness input mac transcript (lifts, table source) := by
  have ratio := programmed_factor_le source inputKey lifts input mac state schedule queries transcript
    fresh reference recordCounts residualCounts priorFits residualFits
  have actual := actual_source_mass_ge bridge mask r1 r2 source inputKey lifts randomizers residues
    input mac randomness transcript compatible referenceActive
  calc
    _ = (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
        ((1 - (2 * transcript.length : Nat) / (Fintype.card Block : ℝ≥0∞)) *
          (sourceFactor source inputKey lifts * fixedTranscriptFactor state.fixedTranscript *
            ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map (fun oracle =>
              programGateSchedule {state with fixedOracle := oracle.1} schedule)).toOuterMeasure
                {programmed | PermutationTranscriptMatches programmed.fixedOracle queries})) := mul_left_comm _ _ _
    _ ≤ _ := le_trans (mul_le_mul' le_rfl (mul_le_mul' le_rfl ratio)) actual

end
end Kriterion.ConditionalDisclosure.CurveSource
