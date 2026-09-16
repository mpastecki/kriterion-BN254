import Proof.ConditionalDisclosureKeySource

namespace Kriterion.ConditionalDisclosure.CurveSource

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] rawBucketUseFintype fixedQueryDomainFintype residualFixedQueryDomainFintype
  publicInputMacKeyFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- The completion count removes exactly the postqueries already covered by active
selected programs, while keeping every remaining public oracle query. -/
def residualFactor [Fintype Block] (source : CurveMaskSample) (baseKey : InputMacKey)
    (lifts : Gate → FullHashLift) (input : AffineInput) (mac : InputMac)
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) : ℝ≥0∞ :=
  ∏ index, ((Fintype.card Block -
    (Fintype.card (RawBucketUse (prescription source baseKey lifts) index) +
      Fintype.card (ResidualFixedQueryDomain (fixedOracleTranscriptRecords transcript)
        (rawActiveDomains (prescription source baseKey lifts) (circuitBucketInputBit input)
          (circuitBucketInputLabel mac mac)) index))).factorial : ℝ≥0∞) /
        (Fintype.card Block).factorial

/-- The actual source at the actual selected input labels dominates the exact
covered-query completion factor. Active agreement is the concrete output of the
selected simulator program; it must still be supplied by the endpoint transport. -/
theorem actual_source_mass_ge [Fintype Block]
    (bridge mask r1 r2 : BaseField) (source : CurveMaskSample) (baseKey : InputMacKey)
    (lifts : Gate → FullHashLift) (randomizers : source.1.1 = ![r1, r2])
    (residues : ∀ gate, field source gate = ((lifts gate).val : BaseField))
    (input : AffineInput) (mac : InputMac) (randomness : Garbling.Randomness)
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible Garbling.oracleHandler randomness transcript)
    (referenceActive : ∀ index, rawSlotBranch index.slot = circuitBucketInputBit input (rawLabelBucket index) →
      ∀ use : RawBucketUse (prescription source baseKey lifts) index,
        randomness.fixedKeyOracle.permutation index
          (circuitBucketInputLabel mac mac (rawLabelBucket index) ^^^
            rawBucketTweak (prescription source baseKey lifts) index use) =
          rawBucketOffset (prescription source baseKey lifts) index use ^^^
            circuitBucketInputLabel mac mac (rawLabelBucket index)) :
    (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
      ((1 - (2 * transcript.length : Nat) / (Fintype.card Block : ℝ≥0∞)) *
        residualFactor source baseKey lifts input mac transcript) ≤
    (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
      {sample | sample.2.encodeAffine input = mac ∧
        actual bridge mask r1 r2 sample.1 sample.2 = (lifts, table source) ∧
        OracleTranscriptCompatible Garbling.oracleHandler
          {randomness with fixedKeyOracle := sample.1} transcript} := by
  rw [actual_source_key_mass bridge mask r1 r2 source lifts randomizers residues
    input mac randomness transcript]
  have mass := inactive_realTranscript_mass_ge source baseKey lifts
    (circuitBucketInputBit input) circuitBucketWire (fun _ => 0)
    (circuitBucketInputLabel mac mac) randomness transcript compatible referenceActive
  simp_rw [mixed_prescription_eq] at mass
  exact mul_le_mul' le_rfl mass

end
end Kriterion.ConditionalDisclosure.CurveSource
