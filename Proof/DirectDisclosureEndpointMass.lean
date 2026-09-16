import Construction.DirectDisclosureScheme
import Proof.DirectDisclosureSimulator
import Proof.Privacy.Source.CrossSourceMass

namespace Kriterion.DirectDisclosure.Endpoint

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The actual real source event retains the entire public CDS table, actual selected
input labels, and both adversary transcript phases. -/
def realSource (witness : Garbling.Randomness) (parameter : Nat) (scalar : NonZeroScalar)
    (table : Public) (input : AffineInput) (mac : InputMac)
    (before after : List (Sigma Garbling.oracleSpec.Answer)) : ℝ≥0∞ :=
  (randomTape witness parameter).toOuterMeasure {randomness |
    garble scalar.value randomness = table ∧ randomness.inputMacKey.encodeAffine input = mac ∧
      OracleTranscriptCompatible Garbling.oracleHandler randomness (before ++ after)}

/-- The fixed transcript factors are common to the real and ideal endpoints.
This equation uses the ACTUAL scheme garbler and encoding, not an abstract replacement. -/
theorem real_mass_factor [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : NonZeroScalar) (witness : Garbling.Randomness)
    (table : Public) (referenceBefore referenceAfter : SimulatorState)
    (selected : AffineInput × adversary.State) (labels : Garbling.Labels) (decision : Bool)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    (firstCompatible : OracleTranscriptCompatible idealOracleHandler referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible idealOracleHandler referenceAfter after) :
    (realAdaptiveTranscriptWithState internalScheme (randomTape witness) Garbling.oracleHandler
      adversary parameter scalar auxiliary) (table, selected, before, labels, decision, after) =
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.chooseInput parameter table auxiliary) referenceBefore).map
        (fun output => (output.1, output.2.2))) (selected, before) *
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.decide parameter table labels auxiliary selected.2) referenceAfter).map
        (fun output => (output.1, output.2.2))) (decision, after) *
    (if labels.input = BitInput.ofAffine selected.1 then
      realSource witness parameter scalar table selected.1 labels.inputMac before after else 0) := by
  rw [realAdaptiveTranscriptWithState,
    sampledTwoPhaseTranscript_mass_factor_cross Garbling.oracleHandler idealOracleHandler
      (randomTape witness parameter)
      (fun randomness => (internalScheme.garble parameter scalar randomness).1) id
      (fun table => adversary.chooseInput parameter table auxiliary)
      (fun randomness state selected => PMF.pure
        (internalScheme.encode (internalScheme.garble parameter scalar randomness).2 selected.1, state))
      (fun table selected labels => adversary.decide parameter table labels auxiliary selected.2)
      referenceBefore referenceAfter table selected labels decision before after firstCompatible secondCompatible,
    sampledTwoPhaseSourceMass_real]
  congr 1
  unfold realSource
  have labelsEq (randomness : Garbling.Randomness) :
      internalScheme.encode (internalScheme.garble parameter scalar randomness).2 selected.1 = labels ↔
        labels.input = BitInput.ofAffine selected.1 ∧
          randomness.inputMacKey.encodeAffine selected.1 = labels.inputMac := by
    cases labels
    simp only [internalScheme, Garbling.Labels.mk.injEq, eq_comm]
  by_cases same : labels.input = BitInput.ofAffine selected.1
  · rw [if_pos same]
    congr 1
    ext randomness
    simp only [Set.mem_setOf_eq, labelsEq, same, true_and]
    rfl
  · rw [if_neg same]
    have empty : {randomness : Garbling.Randomness |
        (internalScheme.garble parameter scalar randomness).1 = table ∧
        internalScheme.encode (internalScheme.garble parameter scalar randomness).2 selected.1 = labels ∧
        OracleTranscriptCompatible Garbling.oracleHandler (id randomness) (before ++ after)} = ∅ := by
      ext randomness
      simp only [Set.mem_setOf_eq, labelsEq, same, false_and, and_false, Set.mem_empty_iff_false]
    rw [empty]
    simp

/-- This is the actual online simulator source, including its selected curve programming after the first transcript. -/
def idealSource [FieldCertificate] [GroupCertificate] {Aux : Type}
    (parameter : Nat) (scalar : NonZeroScalar)
    (table : Public) (selected : AffineInput × Aux) (labels : Garbling.Labels)
    (before after : List (Sigma Garbling.oracleSpec.Answer)) : ℝ≥0∞ :=
  sampledTwoPhaseSourceMass Simulation.handler
    (Simulation.simulator.simulateGarble parameter (topology scalar)) Prod.fst Prod.snd
    (fun _ state selected => Simulation.simulator.simulateEncode state selected.1
      (internalScheme.function scalar selected.1)) table selected labels before after

/-- The ideal endpoint has exactly the same adversary factors and its actual source mass.
The remaining security work is a bound comparing these two source factors. -/
theorem ideal_mass_factor [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (scalar : NonZeroScalar)
    (table : Public) (referenceBefore referenceAfter : SimulatorState)
    (selected : AffineInput × adversary.State) (labels : Garbling.Labels) (decision : Bool)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    (firstCompatible : OracleTranscriptCompatible idealOracleHandler referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible idealOracleHandler referenceAfter after) :
    (idealAdaptiveTranscriptWithState internalScheme topology Simulation.simulator Simulation.handler
      adversary parameter scalar auxiliary) (table, selected, before, labels, decision, after) =
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.chooseInput parameter table auxiliary) referenceBefore).map
        (fun output => (output.1, output.2.2))) (selected, before) *
    ((runOracleProgramWithTranscript idealOracleHandler
      (adversary.decide parameter table labels auxiliary selected.2) referenceAfter).map
        (fun output => (output.1, output.2.2))) (decision, after) *
    idealSource parameter scalar table selected labels before after := by
  rw [idealAdaptiveTranscriptWithState, sampledTwoPhaseTranscript_mass_factor_cross
    Simulation.handler idealOracleHandler
    (Simulation.simulator.simulateGarble parameter (topology scalar)) Prod.fst Prod.snd
    (fun table => adversary.chooseInput parameter table auxiliary)
    (fun _ state selected => Simulation.simulator.simulateEncode state selected.1
      (internalScheme.function scalar selected.1))
    (fun table selected labels => adversary.decide parameter table labels auxiliary selected.2)
    referenceBefore referenceAfter table selected labels decision before after firstCompatible secondCompatible]
  rfl

end
end Kriterion.DirectDisclosure.Endpoint
