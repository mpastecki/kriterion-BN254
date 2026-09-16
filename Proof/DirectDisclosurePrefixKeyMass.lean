import Proof.DirectDisclosureJointKey

namespace Kriterion.DirectDisclosure.Endpoint

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] publicInputMacKeyFintype Classical.propDecidable transcriptOracleFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- The exact joint fixed-oracle/key prefix and selected-program mass. All nonfixed
oracle conditions remain in the compatible transcript event. The key-grid condition
is evaluated on the actual retained prefix, then transported to its compatible reference. -/
theorem prefix_key_grid_mass [Fintype Block]
    (initial : SimulatorState) (randomness : Garbling.Randomness)
    (request : CurveGateRequest) (input : AffineInput) (mac : InputMac)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    (empty : initial.fixedTranscript = [])
    (enc : initial.encOracle = randomness.encPRFOracle)
    (hash : initial.hashOracle = randomness.hashOracle)
    (compatible : OracleTranscriptCompatible idealOracleHandler initial before)
    [Nonempty (TranscriptOracle (transcriptFinalState idealOracleHandler initial before).fixedTranscript)] :
    ((PMF.uniformOfFintype (PermutationOracle Pipeline.FixedKeyIndex Block)).bind fun oracle =>
      (PMF.uniformOfFintype InputMacKey).map fun key => (oracle, key)).toOuterMeasure {pair |
        pair.2.encodeAffine input = mac ∧
        ¬ LabelCollision.GridCollision
          (transcriptFinalState idealOracleHandler {initial with fixedOracle := pair.1} before).fixedTranscript
          (LabelCollision.selectedUses request input) pair.2 ∧
        OracleTranscriptCompatible idealOracleHandler {initial with fixedOracle := pair.1} before ∧
        OracleTranscriptCompatible idealOracleHandler
          (programGateSchedule
            (transcriptFinalState idealOracleHandler {initial with fixedOracle := pair.1} before)
            (request.schedule input (pair.2.encodeAffine input))) after} =
      if ¬ LabelCollision.GridCollision
        (transcriptFinalState idealOracleHandler initial before).fixedTranscript
        (LabelCollision.selectedUses request input)
        (selectedPublicKey input (inputMacCoordinateEquiv mac)) then
          (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
          fixedTranscriptFactor (transcriptFinalState idealOracleHandler initial before).fixedTranscript *
          ((PMF.uniformOfFintype (TranscriptOracle
            (transcriptFinalState idealOracleHandler initial before).fixedTranscript)).map fun oracle =>
              programGateSchedule
                {transcriptFinalState idealOracleHandler initial before with fixedOracle := oracle.1}
                (request.schedule input mac)).toOuterMeasure
                  {programmed | OracleTranscriptCompatible idealOracleHandler programmed after}
      else 0 := by
  rw [selected_key_grid_joint_event
    (PMF.uniformOfFintype (PermutationOracle Pipeline.FixedKeyIndex Block)) (fun _ => request)
    (fun oracle => (transcriptFinalState idealOracleHandler {initial with fixedOracle := oracle} before).fixedTranscript)
    input mac (fun oracle selectedMac =>
      OracleTranscriptCompatible idealOracleHandler {initial with fixedOracle := oracle} before ∧
      OracleTranscriptCompatible idealOracleHandler
        (programGateSchedule
          (transcriptFinalState idealOracleHandler {initial with fixedOracle := oracle} before)
          (request.schedule input selectedMac)) after)]
  let good := ¬ LabelCollision.GridCollision
    (transcriptFinalState idealOracleHandler initial before).fixedTranscript
    (LabelCollision.selectedUses request input)
    (selectedPublicKey input (inputMacCoordinateEquiv mac))
  have event_eq : {oracle : PermutationOracle Pipeline.FixedKeyIndex Block |
      ¬ LabelCollision.GridCollision
        (transcriptFinalState idealOracleHandler {initial with fixedOracle := oracle} before).fixedTranscript
        (LabelCollision.selectedUses request input)
        (selectedPublicKey input (inputMacCoordinateEquiv mac)) ∧
      OracleTranscriptCompatible idealOracleHandler {initial with fixedOracle := oracle} before ∧
      OracleTranscriptCompatible idealOracleHandler
        (programGateSchedule
          (transcriptFinalState idealOracleHandler {initial with fixedOracle := oracle} before)
          (request.schedule input mac)) after} =
      {oracle | good ∧ OracleTranscriptCompatible idealOracleHandler {initial with fixedOracle := oracle} before ∧
        OracleTranscriptCompatible idealOracleHandler
          (programGateSchedule
            (transcriptFinalState idealOracleHandler {initial with fixedOracle := oracle} before)
            (request.schedule input mac)) after} := by
    ext oracle
    simp only [Set.mem_ofPred_eq]
    by_cases prior : OracleTranscriptCompatible idealOracleHandler {initial with fixedOracle := oracle} before
    · have same := idealTranscriptFinal_updateFixed initial oracle before compatible prior
      rw [same]
    · simp only [prior, false_and, and_false]
  rw [event_eq]
  by_cases valid : good
  · rw [if_pos valid]
    have events : {oracle : PermutationOracle Pipeline.FixedKeyIndex Block |
        good ∧ OracleTranscriptCompatible idealOracleHandler {initial with fixedOracle := oracle} before ∧
        OracleTranscriptCompatible idealOracleHandler
          (programGateSchedule
            (transcriptFinalState idealOracleHandler {initial with fixedOracle := oracle} before)
            (request.schedule input mac)) after} =
        {oracle | OracleTranscriptCompatible idealOracleHandler {initial with fixedOracle := oracle} before ∧
          OracleTranscriptCompatible idealOracleHandler
            (programGateSchedule
              (transcriptFinalState idealOracleHandler {initial with fixedOracle := oracle} before)
              (request.schedule input mac)) after} := by
      ext oracle
      simp only [Set.mem_ofPred_eq, valid, true_and]
    rw [events, idealPrefixProgrammed_mass initial randomness before after
      (request.schedule input mac) empty enc hash compatible, mul_assoc]
  · rw [if_neg valid]
    have events : {oracle : PermutationOracle Pipeline.FixedKeyIndex Block |
        good ∧ OracleTranscriptCompatible idealOracleHandler {initial with fixedOracle := oracle} before ∧
        OracleTranscriptCompatible idealOracleHandler
          (programGateSchedule
            (transcriptFinalState idealOracleHandler {initial with fixedOracle := oracle} before)
            (request.schedule input mac)) after} = ∅ := by
      ext oracle
      simp only [Set.mem_ofPred_eq, valid, false_and, Set.mem_empty_iff_false]
    rw [events]
    simp

end
end Kriterion.DirectDisclosure.Endpoint
