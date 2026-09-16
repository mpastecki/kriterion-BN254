import Solution
import Construction
import Proof

namespace Submission
open Kriterion Kriterion.BN254 Kriterion.ArgoMAC

/-- The wire adapter preserves the complete ciphertext and removes repeated input bits. -/
def solution : Kriterion.Solution := {
  FixedIndex := Pipeline.FixedKeyIndex
  EncIndex := EncPRF.PermutationIndex
  fixedFinite := inferInstance
  encFinite := inferInstance
  Randomness := Garbling.Randomness
  randomnessFinite := inferInstance
  randomness := Seed.randomness 0
  Public := Pipeline.Table
  EncodingKey := Garbling.EncodingKey
  State := Security.CircuitSimulatorState
  encoding := Wire.encoding
  ciphertextBytes := 8956916
  evaluationOracle := fun tape => (tape.fixedKeyOracle, tape.encPRFOracle, tape.hashOracle)
  oracleUniform := by
    convert Security.oracleUniform (Seed.randomness 0) using 1
  scheme := fun field group => @Lamport.wireCircuit field group
  ciphertextSize := by
    intro field group parameter scalar tape
    dsimp only [Lamport.wireCircuit, GarbledCircuit.mapLabels, Garbling.garbledCircuit]
    have size := Wire.garble_length construction scalar tape
    simpa only [Garbling.PublicCircuit] using size
  lamportCompatible := fun field group => @Lamport.compatible field group
  idealOracle := Security.circuitSimulatorOracleHandler
  idealView := Security.CircuitSimulatorState.view
  functionCorrect := fun _ _ _ _ => rfl
  perfectCorrectness := by
    intro field group parameter scalar tape input
    letI := field
    letI := group
    change some (Garbling.evaluate _ _ (Lamport.restore input
      (Lamport.selectedLabels (tape.inputMacKey.encodeAffine input)))) = _
    rw [Lamport.restore_selected]
    exact RCBComplete.perfectCorrectness parameter scalar tape input
  adaptivePrivacy := by
    intro field group
    letI := field
    letI := group
    let pack := fun labels : Garbling.Labels => Lamport.selectedLabels labels.inputMac
    let restore := fun _ : Nat => (⟨508, 91⟩ : Garbling.Topology)
    refine ⟨Security.concreteCircuitSimulator.mapLabels pack restore,
      Security.concreteCircuitSimulator_rules.mapLabels pack restore, ?_⟩
    have privacy := (Security.concreteAdaptivePrivacy (Aux := Unit) (Seed.randomness 0)).mapLabels
      pack Lamport.restore (fun _ => 8956916) restore (fun _ => rfl)
    have instances : (@Fintype.ofFinite Garbling.Randomness inferInstance) =
        Security.garblingRandomnessFintype := Subsingleton.elim _ _
    have tapes : @uniformRandomTape Garbling.Randomness (@Fintype.ofFinite _ inferInstance)
        (Seed.randomness 0) = Security.randomTape (Seed.randomness 0) := by
      unfold uniformRandomTape Security.randomTape
      rw [Cryptography.uniformTape_eq, instances]
    rw [tapes]
    exact privacy
}

end Submission
