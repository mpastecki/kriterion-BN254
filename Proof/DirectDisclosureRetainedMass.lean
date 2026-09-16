import Proof.DirectDisclosureRetainedEvent

namespace Kriterion.DirectDisclosure.SourceKernel

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype transcriptOracleFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
variable [Fintype Block]

/-- The remaining joint event after the static source/table/input guards. -/
def retainedJointEvent (scalar : ScalarField) (rest : GarblingSourceRest) (tag : FullTag)
    (input : AffineInput) (mac : InputMac) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (sample : OracleKey) : Prop :=
  sample.2.encodeAffine input = mac ∧
    ¬ LabelCollision.GridCollision
      (transcriptFinalState idealOracleHandler (pairInitial rest sample.1) before).fixedTranscript
      (LabelCollision.selectedUses (retainedRequest scalar rest tag input) input) sample.2 ∧
    OracleTranscriptCompatible idealOracleHandler (pairInitial rest sample.1) before ∧
    OracleTranscriptCompatible idealOracleHandler
      (programGateSchedule (transcriptFinalState idealOracleHandler (pairInitial rest sample.1) before)
        ((retainedRequest scalar rest tag input).schedule input (sample.2.encodeAffine input))) after

private theorem static_guards {A : Type} (samples : PMF A) (P Q R : Prop) [Decidable P] [Decidable Q] [Decidable R] (event : A → Prop) :
    samples.toOuterMeasure {a | P ∧ Q ∧ R ∧ event a} =
      if P ∧ Q ∧ R then samples.toOuterMeasure {a | event a} else 0 := by
  by_cases p : P <;> by_cases q : Q <;> by_cases r : R <;> simp [p, q, r]

theorem retained_good_mass_guard {Aux : Type} (scalar : ScalarField) (rest : GarblingSourceRest) (tag : FullTag)
    (publicTable : Public) (selected : AffineInput × Aux) (labels : Garbling.Labels)
    (before after : List (Sigma Garbling.oracleSpec.Answer)) :
    (PMF.uniformOfFintype OracleKey).toOuterMeasure
      {sample | retainedGoodEvent scalar rest tag publicTable selected labels before after sample} =
      if ConditionalDisclosure.CurveSource.Complete tag.1 ∧ retainedTable scalar rest tag = publicTable ∧
        BitInput.ofAffine selected.1 = labels.input then
          (PMF.uniformOfFintype OracleKey).toOuterMeasure
            {sample | retainedJointEvent scalar rest tag selected.1 labels.inputMac before after sample}
      else 0 := by
  unfold retainedGoodEvent
  exact static_guards (PMF.uniformOfFintype OracleKey)
    (ConditionalDisclosure.CurveSource.Complete tag.1) (retainedTable scalar rest tag = publicTable)
    (BitInput.ofAffine selected.1 = labels.input)
    (retainedJointEvent scalar rest tag selected.1 labels.inputMac before after)

private theorem uniform_pair_order :
    PMF.uniformOfFintype OracleKey =
      (PMF.uniformOfFintype (PermutationOracle Pipeline.FixedKeyIndex Block)).bind fun oracle =>
        (PMF.uniformOfFintype InputMacKey).map fun key => (oracle, key) := by
  rw [uniform_prod_eq_bind]
  exact PMF.bind_comm (PMF.uniformOfFintype InputMacKey)
    (PMF.uniformOfFintype (PermutationOracle Pipeline.FixedKeyIndex Block))
    (fun key oracle => PMF.pure (oracle, key))

/-- The exact retained fixed/key source event has the conditional program density;
all source masks, public rows and nonfixed oracle replies are retained. -/
theorem retained_joint_mass (scalar : ScalarField) (rest : GarblingSourceRest) (tag : FullTag)
    (input : AffineInput) (mac : InputMac) (reference : PermutationOracle Pipeline.FixedKeyIndex Block)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible idealOracleHandler (pairInitial rest reference) before)
    [Nonempty (TranscriptOracle
      (transcriptFinalState idealOracleHandler (pairInitial rest reference) before).fixedTranscript)] :
    (PMF.uniformOfFintype OracleKey).toOuterMeasure
      {sample | retainedJointEvent scalar rest tag input mac before after sample} =
      if ¬ LabelCollision.GridCollision
        (transcriptFinalState idealOracleHandler (pairInitial rest reference) before).fixedTranscript
        (LabelCollision.selectedUses (retainedRequest scalar rest tag input) input)
        (selectedPublicKey input (inputMacCoordinateEquiv mac)) then
          (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
          fixedTranscriptFactor (transcriptFinalState idealOracleHandler (pairInitial rest reference) before).fixedTranscript *
          ((PMF.uniformOfFintype (TranscriptOracle
            (transcriptFinalState idealOracleHandler (pairInitial rest reference) before).fixedTranscript)).map fun oracle =>
              programGateSchedule
                {transcriptFinalState idealOracleHandler (pairInitial rest reference) before with fixedOracle := oracle.1}
                ((retainedRequest scalar rest tag input).schedule input mac)).toOuterMeasure
                  {programmed | OracleTranscriptCompatible idealOracleHandler programmed after}
      else 0 := by
  rw [uniform_pair_order]
  simpa only [retainedJointEvent, pairInitial, initial] using
    (Endpoint.prefix_key_grid_mass (pairInitial rest reference) rest.reference
      (retainedRequest scalar rest tag input) input mac before after rfl rfl rfl compatible)

end
end Kriterion.DirectDisclosure.SourceKernel
