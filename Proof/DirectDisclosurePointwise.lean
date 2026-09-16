import Proof.DirectDisclosureGlobalSourceBound
import Proof.DirectDisclosureFlaggedWitness
import Proof.DirectDisclosureFlaggedLength
import Proof.DirectDisclosurePrivacyClosure

namespace Kriterion.DirectDisclosure

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

private theorem zero_product (loss first second target : ℝ≥0∞) : loss * (first * second * 0) ≤ target := by
  rw [mul_zero, mul_zero]
  exact bot_le

/-- The actual virtual good-source comparison is summed through both adversary
phases, with every unsupported transcript handled by its exact zero mass. -/
theorem actual_small_pointwise [FieldCertificate] [GroupCertificate] {Aux : Type}
    (witness : Garbling.Randomness) : PrivacyClosure.SmallPointwiseBounds (Aux := Aux) witness := by
  intro adversary parameter scalar auxiliary small transcript
  rcases transcript with ⟨publicTable, selected, before, labels, decision, after⟩
  let q := adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter
  let output : SourceKernel.Transcript adversary.State × Bool :=
    ((publicTable, selected, before, labels, decision, after), false)
  by_cases zero : SourceKernel.fullFlagged adversary parameter scalar.value auxiliary output = 0
  · rw [zero, mul_zero]
    exact bot_le
  · have virtualNonzero : SourceKernel.virtualTranscript witness adversary parameter scalar.value auxiliary output ≠ 0 := by
      rw [← SourceKernel.fullFlagged_virtual]
      exact zero
    have references := FlaggedMass.nonzero_references idealOracleHandler
      (SourceKernel.virtualSamples witness parameter)
      (fun source => SourceKernel.tableOf scalar.value (Randomness.tapeSeed source.1) source.2)
      (fun source => SourceKernel.initial (Randomness.tapeSeed source.1).oracles)
      (fun table => adversary.chooseInput parameter table auxiliary)
      (fun source state chosen => SourceKernel.sourceEncode scalar.value source state chosen.1)
      (fun table chosen lab => adversary.decide parameter table lab auxiliary chosen.2)
      output virtualNonzero
    obtain ⟨referenceBefore, referenceAfter, firstCompatible, secondCompatible⟩ := references
    have bounded : (before ++ after).length ≤ q :=
      FlaggedMass.append_length_le idealOracleHandler
        (SourceKernel.virtualSamples witness parameter)
        (fun source => SourceKernel.tableOf scalar.value (Randomness.tapeSeed source.1) source.2)
        (fun source => SourceKernel.initial (Randomness.tapeSeed source.1).oracles)
        (fun table => adversary.chooseInput parameter table auxiliary)
        (fun source state chosen => SourceKernel.sourceEncode scalar.value source state chosen.1)
        (fun table chosen lab => adversary.decide parameter table lab auxiliary chosen.2)
        output virtualNonzero
    rw [SourceKernel.fullFlagged_good_mass_factor witness adversary parameter scalar.value auxiliary
      publicTable selected labels decision before after referenceBefore referenceAfter firstCompatible secondCompatible]
    by_cases bits : labels.input = BitInput.ofAffine selected.1
    · rw [Endpoint.real_mass_factor adversary parameter auxiliary scalar witness publicTable referenceBefore referenceAfter
        selected labels decision before after firstCompatible secondCompatible, if_pos bits]
      have card : Fintype.card Block = 2 ^ 128 :=
        (Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin _)
      have lossLe : 1 - 2 * (q : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128 ≤
          1 - (2 * (before ++ after).length : Nat) / (Fintype.card Block : ℝ≥0∞) := by
        apply tsub_le_tsub_left
        rw [card, Nat.cast_pow, Nat.cast_ofNat]
        apply ENNReal.div_le_div_right
        exact_mod_cast Nat.mul_le_mul_left 2 bounded
      have sourceBound := SourceKernel.virtual_good_source_le witness parameter scalar publicTable selected labels
        referenceBefore before after firstCompatible q small bounded
      have comparison := (mul_le_mul' lossLe
        (le_rfl : SourceKernel.virtualGoodSource witness parameter scalar.value publicTable selected labels before after ≤ _)).trans sourceBound
      rw [mul_left_comm]
      exact mul_le_mul' le_rfl comparison
    · rw [SourceKernel.virtualGoodSource_bits_zero witness parameter scalar.value publicTable selected labels before after bits]
      exact zero_product _ _ _ _

/-- Complete unchanged adaptive privacy for the direct disclosure construction. -/
theorem adaptivePrivacy [FieldCertificate] [GroupCertificate] {Aux : Type}
    (witness : Garbling.Randomness) :
    GarbledCircuit.ConcreteAdaptivePrivacy (Aux := Aux) internalScheme topology Simulation.simulator
      (randomTape witness) Garbling.oracleHandler Simulation.handler 100 :=
  PrivacyClosure.privacy_of_pointwise witness (actual_small_pointwise witness)

end
end Kriterion.DirectDisclosure
