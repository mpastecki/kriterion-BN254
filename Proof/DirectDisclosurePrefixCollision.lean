import Proof.DirectDisclosurePrefix
import Proof.DirectDisclosureScheduleCollision
import Cryptography.Probability

namespace Kriterion.DirectDisclosure.Simulation.Prefix

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] publicInputMacKeyFintype Classical.propDecidable
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

def gridBad [FieldCertificate] [GroupCertificate]
    (state : Simulation.State) (input : AffineInput) (output : Option Point) : Prop :=
  LabelCollision.GridCollision state.oracle.fixedTranscript
    (LabelCollision.selectedUses (state.selectedCurve input output) input) state.inputKey

/-- The actual pre-label simulator history can collide with the entire curve grid
only through a uniform shifted label. No independence premise about the prefix is assumed. -/
theorem actualPrefix_grid_bad_le [FieldCertificate] [GroupCertificate] [Fintype Block] {Aux : Type*}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (output : AffineInput → Option Point) :
    (actualPrefix adversary parameter auxiliary).toOuterMeasure
      {result | gridBad result.2.2 result.2.1.1 (output result.2.1.1)} ≤
      (12700 * adversary.firstQueryBudget parameter : Nat) / (Fintype.card Block : ℝ≥0∞) := by
  rw [actualPrefix_factorization]
  unfold separatedPrefix
  apply Probability.bind_event_le
  intro frame _
  apply Probability.bind_event_le
  intro selected member
  rw [uniform_prod_eq_bind, PMF.map_bind]
  apply Probability.bind_event_le
  intro target _
  rw [PMF.map_comp, PMF.toOuterMeasure_map_apply]
  change (PMF.uniformOfFintype InputMacKey).toOuterMeasure
    {key | LabelCollision.GridCollision selected.2.fixedTranscript
      (LabelCollision.selectedUses
        (frame.1.request.retarget selected.1.1
          (if OnCurve selected.1.1 then embedScalar (ScalarRecovery.recover selected.1.1 (output selected.1.1))
            else target)) selected.1.1) key} ≤ _
  have lengthBound := LabelCollision.fixed_history_length
    (adversary.chooseInput parameter (frameTable frame) auxiliary) (initialOracle frame) selected member
  have bounded : selected.2.fixedTranscript.length ≤ adversary.firstQueryBudget parameter := by
    simpa only [initialOracle, List.length_nil, Nat.zero_add] using lengthBound
  apply (LabelCollision.grid_collision_mass_le _ _).trans
  apply ENNReal.div_le_div_right
  exact_mod_cast Nat.mul_le_mul_left 12700 bounded

end
end Kriterion.DirectDisclosure.Simulation.Prefix
