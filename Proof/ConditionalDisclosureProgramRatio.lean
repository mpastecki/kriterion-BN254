import Proof.ConditionalDisclosureKeyRatio
import Proof.Privacy.Transcript.AdaptiveGameRatio

namespace Kriterion.ConditionalDisclosure.CurveSource

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] rawBucketUseFintype fixedQueryDomainFintype residualFixedQueryDomainFintype
  transcriptOracleFintype

def uses (source : CurveMaskSample) (inputKey : InputMacKey) (lifts : Gate → FullHashLift)
    (index : Pipeline.FixedKeyIndex) : Nat :=
  Fintype.card (RawBucketUse (prescription source inputKey lifts) index)

/-- The complete source's block-density factor is retained before conditional programming. -/
def sourceFactor [Fintype Block] (source : CurveMaskSample) (inputKey : InputMacKey)
    (lifts : Gate → FullHashLift) : ℝ≥0∞ :=
  ∏ index, ((Fintype.card Block : ℝ≥0∞) ^ uses source inputKey lifts index)⁻¹

/-- Exact record counts and residual-domain equality transport the actual selected
program's probability to the real completion factor. These are structural schedule
facts, not additional cryptographic assumptions. -/
theorem programmed_factor_le [Fintype Block]
    (source : CurveMaskSample) (inputKey : InputMacKey) (lifts : Gate → FullHashLift)
    (input : AffineInput) (mac : InputMac)
    (state : SimulatorState) (schedule : List GateDirective)
    (queries : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
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
    sourceFactor source inputKey lifts * fixedTranscriptFactor state.fixedTranscript *
      ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map (fun oracle =>
        programGateSchedule {state with fixedOracle := oracle.1} schedule)).toOuterMeasure
          {programmed | PermutationTranscriptMatches programmed.fixedOracle queries} ≤
      residualFactor source inputKey lifts input mac transcript := by
  let active := fun index : Pipeline.FixedKeyIndex =>
    decide (rawSlotBranch index.slot = circuitBucketInputBit input (rawLabelBucket index))
  unfold sourceFactor
  rw [programGateSchedule_sourceMass_product state schedule queries fresh reference
    (uses source inputKey lifts) active (fun index => by
      simpa only [active, decide_eq_true_eq] using recordCounts index)]
  have bound := adaptiveIdealPermutationFactor_le (Fintype.card Block)
    (uses source inputKey lifts)
    (fun index => Fintype.card (FixedQueryDomain state.fixedTranscript index))
    (fun index => Fintype.card (ResidualFixedQueryDomain (state.fixedTranscript ++ queries)
      (programmedDomains (gateProgramRecords schedule)) index)) active Fintype.card_pos priorFits residualFits
  apply bound.trans_eq
  unfold residualFactor
  apply Finset.prod_congr rfl
  intro index _
  simp only [residualCounts, uses]

end
end Kriterion.ConditionalDisclosure.CurveSource
