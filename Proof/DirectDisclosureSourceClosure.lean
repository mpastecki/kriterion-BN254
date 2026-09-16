import Proof.DirectDisclosureTagRatio
import Proof.DirectDisclosureReferenceActive
import Proof.DirectDisclosureProgramDomains
import Proof.DirectDisclosureProgramSupport
import Proof.Privacy.Source.ActualAdaptiveRatio

namespace Kriterion.ConditionalDisclosure.CurveSource

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable rawBucketUseFintype fixedQueryDomainFintype
  residualFixedQueryDomainFintype transcriptOracleFintype publicInputMacKeyFintype

/-- The selected schedule is formed from the complete retained actual curve source. -/
def selectedSchedule (bridge mask : BaseField) (source : CurveMaskSample)
    (inputKey : InputMacKey) (input : AffineInput) : List GateDirective :=
  (curveMaskSampleGarble bridge mask input source).request.schedule input (inputKey.encodeAffine input)

/-- All count, domain, and active-source premises are discharged for the actual
selected curve schedule. Only prefix freshness, capacities, and the retained external
transcript conditions remain for the adaptive support lemmas. -/
theorem selected_source_mass_le
    (bridge mask r1 r2 : BaseField) (source : CurveMaskSample)
    (randomizers : source.1.1 = ![r1, r2]) (inputKey : InputMacKey) (input : AffineInput)
    (state : SimulatorState) (randomness : Garbling.Randomness)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    [Nonempty (TranscriptOracle state.fixedTranscript)]
    (nonfixed : NonFixedTranscriptCompatible randomness (before ++ after))
    (members : ∀ record, record ∈ state.fixedTranscript ↔ record ∈ fixedOracleTranscriptRecords before)
    (fresh : FreshRecordSchedule state.fixedTranscript
      (gateProgramRecords (selectedSchedule bridge mask source inputKey input)))
    (priorFits : ∀ index, uses source inputKey (selectedLifts source) index +
      Fintype.card (FixedQueryDomain state.fixedTranscript index) ≤ Fintype.card Block)
    (residualFits : ∀ index, uses source inputKey (selectedLifts source) index +
      Fintype.card (ResidualFixedQueryDomain
        (state.fixedTranscript ++ fixedOracleTranscriptRecords after)
        (programmedDomains (gateProgramRecords (selectedSchedule bridge mask source inputKey input))) index) ≤
          Fintype.card Block) :
    (1 - (2 * (before ++ after).length : Nat) / (Fintype.card Block : ℝ≥0∞)) *
      ((Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
        (sourceFactor source inputKey (selectedLifts source) * fixedTranscriptFactor state.fixedTranscript *
          ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map (fun oracle =>
            programGateSchedule {state with fixedOracle := oracle.1}
              (selectedSchedule bridge mask source inputKey input))).toOuterMeasure
                {programmed | PermutationTranscriptMatches programmed.fixedOracle (fixedOracleTranscriptRecords after)})) ≤
      tagMass bridge mask r1 r2 randomness input (inputKey.encodeAffine input) (before ++ after)
        (selectedLifts source, table source) := by
  let schedule := selectedSchedule bridge mask source inputKey input
  by_cases existsReference : Nonempty (TranscriptOracle
      (programRecordHistory state.fixedTranscript (gateProgramRecords schedule) ++ fixedOracleTranscriptRecords after))
  · let reference := Classical.choice existsReference
    have matching : PermutationTranscriptMatches reference.1 (fixedOracleTranscriptRecords (before ++ after)) ∧
        PermutationTranscriptMatches reference.1 (gateProgramRecords schedule) := by
      constructor
      · intro record member
        rw [fixedOracleTranscriptRecords_append, List.mem_append] at member
        apply reference.2 record
        rcases member with old | later
        · exact List.mem_append_left _ ((mem_programRecordHistory_iff _ _ _).mpr (Or.inr ((members record).mpr old)))
        · exact List.mem_append_right _ later
      · intro record member
        exact reference.2 record (List.mem_append_left _ ((mem_programRecordHistory_iff _ _ _).mpr (Or.inl member)))
    have compatible : OracleTranscriptCompatible Garbling.oracleHandler
        {randomness with fixedKeyOracle := reference.1} (before ++ after) := by
      rw [realOracleTranscriptCompatible_iff, nonFixedTranscriptCompatible_update]
      exact ⟨matching.1, nonfixed⟩
    have residues : ∀ gate, field source gate = ((selectedLifts source gate).val : BaseField) :=
      fun gate => goodHashLiftSource_field (field source gate, source.2.2 gate.1 gate.2) |>.symm
    have active := reference_active bridge mask source inputKey input reference.1 matching.2
    have counts := program_domain_count (curveMaskSampleGarble bridge mask input source).request input
      (inputKey.encodeAffine input) source inputKey (selectedLifts source)
    have residual : ∀ index,
        Fintype.card (ResidualFixedQueryDomain (state.fixedTranscript ++ fixedOracleTranscriptRecords after)
          (programmedDomains (gateProgramRecords schedule)) index) =
        Fintype.card (ResidualFixedQueryDomain (fixedOracleTranscriptRecords (before ++ after))
          (rawActiveDomains (prescription source inputKey (selectedLifts source)) (circuitBucketInputBit input)
            (circuitBucketInputLabel (inputKey.encodeAffine input) (inputKey.encodeAffine input))) index) := by
      intro index
      have domains := funext (program_domains (curveMaskSampleGarble bridge mask input source).request input
        (inputKey.encodeAffine input) source inputKey (selectedLifts source))
      change _ = _ at domains
      change Fintype.card (ResidualFixedQueryDomain _ (programmedDomains (gateProgramRecords
        ((curveMaskSampleGarble bridge mask input source).request.schedule input (inputKey.encodeAffine input)))) index) = _
      rw [domains]
      apply residualFixedQueryDomain_card_congr
      intro record
      rw [fixedOracleTranscriptRecords_append, List.mem_append, List.mem_append, members]
    exact programmed_tag_mass_le bridge mask r1 r2 {randomness with fixedKeyOracle := reference.1}
      source inputKey (selectedLifts source) randomizers residues input (inputKey.encodeAffine input)
      state schedule (fixedOracleTranscriptRecords after) (before ++ after) compatible active fresh reference
      counts residual priorFits residualFits
  · have zero := programmed_queryMass_zero_of_no_reference state schedule (fixedOracleTranscriptRecords after)
      fresh existsReference
    rw [zero, mul_zero, mul_zero, mul_zero]
    exact bot_le

end
end Kriterion.ConditionalDisclosure.CurveSource
