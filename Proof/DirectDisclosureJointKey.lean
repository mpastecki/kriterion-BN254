import Proof.DirectDisclosureGridRekey

namespace Kriterion.DirectDisclosure.Endpoint

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] publicInputMacKeyFintype Classical.propDecidable
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- Exact selected-key integration under arbitrary retained source data. The
source, request, complete prefix history, and continuation remain jointly observed. -/
theorem selected_key_grid_joint_event [Fintype Block] {A : Type*}
    (samples : PMF A) (request : A → CurveGateRequest)
    (history : A → List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (input : AffineInput) (mac : InputMac) (event : A → InputMac → Prop) :
    (samples.bind fun source =>
      (PMF.uniformOfFintype InputMacKey).map fun key => (source, key)).toOuterMeasure
        {pair | pair.2.encodeAffine input = mac ∧
          ¬ LabelCollision.GridCollision (history pair.1)
            (LabelCollision.selectedUses (request pair.1) input) pair.2 ∧
          event pair.1 (pair.2.encodeAffine input)} =
      (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
        samples.toOuterMeasure {source |
          ¬ LabelCollision.GridCollision (history source)
            (LabelCollision.selectedUses (request source) input)
            (selectedPublicKey input (inputMacCoordinateEquiv mac)) ∧ event source mac} := by
  rw [PMF.toOuterMeasure_bind_apply]
  simp only [PMF.toOuterMeasure_map_apply, Set.preimage_ofPred_eq]
  simp_rw [selected_key_grid_event]
  rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro source
  by_cases good : ¬ LabelCollision.GridCollision (history source)
      (LabelCollision.selectedUses (request source) input)
      (selectedPublicKey input (inputMacCoordinateEquiv mac)) ∧ event source mac
  · simp only [if_pos good, mul_one, Set.indicator_apply, Set.mem_ofPred_eq]
    exact mul_comm _ _
  · simp only [if_neg good, mul_zero, Set.indicator_apply, Set.mem_ofPred_eq]

end
end Kriterion.DirectDisclosure.Endpoint
