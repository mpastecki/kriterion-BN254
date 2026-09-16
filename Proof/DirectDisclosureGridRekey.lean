import Proof.DirectDisclosureScheduleCollision
import Proof.DirectDisclosureSelectedKey

namespace Kriterion.DirectDisclosure

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] publicInputMacKeyFintype Classical.propDecidable
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

namespace LabelCollision

/-- The actual selected grid depends only on the exposed MAC, including both
shifted domain and range coordinates of every slot. -/
theorem grid_rekey (request : CurveGateRequest) (input : AffineInput)
    (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (key1 key2 : InputMacKey) (same : key1.encodeAffine input = key2.encodeAffine input) :
    GridCollision history (selectedUses request input) key1 ↔
      GridCollision history (selectedUses request input) key2 := by
  unfold GridCollision
  apply exists_congr
  intro query
  apply exists_congr
  intro slot
  have first := selectedUses_record request input key1 slot
  have second := selectedUses_record request input key2 slot
  dsimp only at first second ⊢
  rw [first.1, first.2, second.1, second.2, same]

/-- Replacing the unexposed half of a key by the canonical public key preserves
exactly the grid event, with no condition on the unused labels. -/
theorem grid_selectedPublicKey (request : CurveGateRequest) (input : AffineInput)
    (history : List (PermutationRecord Pipeline.FixedKeyIndex Block)) (key : InputMacKey) :
    GridCollision history (selectedUses request input) key ↔
      GridCollision history (selectedUses request input)
        (selectedPublicKey input (inputMacCoordinateEquiv (key.encodeAffine input))) := by
  apply grid_rekey
  rw [selectedPublicKey_encode, Equiv.symm_apply_apply]

end LabelCollision

namespace Endpoint

/-- Exact selected-key integral with the actual good-grid restriction and any
continuation on the complete selected MAC. Both event conditions remain joint. -/
theorem selected_key_grid_event [Fintype Block] (request : CurveGateRequest)
    (input : AffineInput) (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (mac : InputMac) (event : InputMac → Prop) :
    (PMF.uniformOfFintype InputMacKey).toOuterMeasure {key |
      key.encodeAffine input = mac ∧
      ¬ LabelCollision.GridCollision history (LabelCollision.selectedUses request input) key ∧
      event (key.encodeAffine input)} =
      (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
        if ¬ LabelCollision.GridCollision history (LabelCollision.selectedUses request input)
          (selectedPublicKey input (inputMacCoordinateEquiv mac)) ∧ event mac then 1 else 0 := by
  have same : {key : InputMacKey |
      key.encodeAffine input = mac ∧
      ¬ LabelCollision.GridCollision history (LabelCollision.selectedUses request input) key ∧
      event (key.encodeAffine input)} =
      {key | key.encodeAffine input = mac ∧
        (¬ LabelCollision.GridCollision history (LabelCollision.selectedUses request input)
          (selectedPublicKey input (inputMacCoordinateEquiv (key.encodeAffine input))) ∧
        event (key.encodeAffine input))} := by
    ext key
    simp only [Set.mem_ofPred_eq]
    rw [LabelCollision.grid_selectedPublicKey request input history key]
  rw [same]
  convert selected_key_event input mac (fun selected =>
    ¬ LabelCollision.GridCollision history (LabelCollision.selectedUses request input)
      (selectedPublicKey input (inputMacCoordinateEquiv selected)) ∧ event selected) using 1
  split_ifs <;> rfl

end Endpoint
end
end Kriterion.DirectDisclosure
