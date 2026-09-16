import Proof.DirectDisclosureIdealSource
import Proof.Privacy.Source.Valid.ValidSourceKernel

namespace Kriterion.DirectDisclosure.Endpoint

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] publicInputMacKeyFintype Classical.propDecidable
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- Uniform full Lamport keys give exactly uniform selected coordinate labels. -/
theorem selected_key_mass [Fintype Block] (input : AffineInput) (mac : InputMac) :
    (PMF.uniformOfFintype InputMacKey).toOuterMeasure {key | key.encodeAffine input = mac} =
      (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ := by
  have law := map_uniform_selectedLabels input
  have mass := congrArg (fun distribution : PMF (EncPRF.PermutationIndex → Block) =>
    distribution.toOuterMeasure {inputMacCoordinateEquiv mac}) law
  rw [PMF.toOuterMeasure_map_apply] at mass
  simpa only [Set.preimage, Set.mem_singleton_iff, Equiv.apply_eq_iff_eq,
    PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply] using mass

/-- Any continuation that receives only the selected MAC has the exact selected-label
mass. No second independent key or marginal-to-joint inference is used. -/
theorem selected_key_event [Fintype Block] (input : AffineInput) (mac : InputMac)
    (event : InputMac → Prop) :
    (PMF.uniformOfFintype InputMacKey).toOuterMeasure
      {key | key.encodeAffine input = mac ∧ event (key.encodeAffine input)} =
      (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ * if event mac then 1 else 0 := by
  by_cases valid : event mac
  · rw [if_pos valid, mul_one]
    have same : {key : InputMacKey | key.encodeAffine input = mac ∧ event (key.encodeAffine input)} =
        {key | key.encodeAffine input = mac} := by
      ext key
      simp only [Set.mem_setOf_eq]
      exact ⟨And.left, fun equal => ⟨equal, equal.symm ▸ valid⟩⟩
    rw [same, selected_key_mass]
  · rw [if_neg valid, mul_zero]
    have empty : {key : InputMacKey | key.encodeAffine input = mac ∧ event (key.encodeAffine input)} = ∅ := by
      ext key
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨equal, member⟩
      exact valid (equal ▸ member)
    rw [empty]
    simp

/-- This predicate retains the complete before/after oracle conditions while
making the selected MAC the sole label-key dependence. -/
def coinOracleEvent [FieldCertificate] (scalar : ScalarField) (input : AffineInput)
    (mac : InputMac) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (coin : Simulation.Coin) : Prop :=
  OracleTranscriptCompatible idealOracleHandler coin.state.oracle before ∧
    OracleTranscriptCompatible idealOracleHandler
      (programGateSchedule (transcriptFinalState idealOracleHandler coin.state.oracle before)
        ((coin.curve.request.retarget input
          (MaskSource.selectedTarget (embedScalar scalar) input coin.target)).schedule input mac)) after

/-- The oracle event is independent of the unused half of the input key, including
all inverse, EncPRF and hash replies in both transcript phases. -/
theorem coinOracleEvent_rekey [FieldCertificate] (scalar : ScalarField) (input : AffineInput)
    (mac : InputMac) (before after : List (Sigma Garbling.oracleSpec.Answer))
    (coin : Simulation.Coin) (key : InputMacKey) :
    coinOracleEvent scalar input mac before after {coin with inputKey := key} ↔
      coinOracleEvent scalar input mac before after coin := Iff.rfl

/-- This is the exact key integral inside the actual ideal-source event. -/
theorem coinOracleEvent_key_mass [FieldCertificate] [Fintype Block]
    (scalar : ScalarField) (input : AffineInput) (mac : InputMac)
    (before after : List (Sigma Garbling.oracleSpec.Answer)) (coin : Simulation.Coin) :
    (PMF.uniformOfFintype InputMacKey).toOuterMeasure {key |
      key.encodeAffine input = mac ∧
      coinOracleEvent scalar input (key.encodeAffine input) before after {coin with inputKey := key}} =
      (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
        if coinOracleEvent scalar input mac before after coin then 1 else 0 := by
  simp only [coinOracleEvent_rekey]
  exact selected_key_event input mac (fun mac => coinOracleEvent scalar input mac before after coin)

end
end Kriterion.DirectDisclosure.Endpoint
