import Solution
import Construction.ArgoMAC.Seed
import Proof.DirectDisclosureCorrectness
import Proof.DirectDisclosureSimulator
import Proof.Privacy.Distribution.Distribution

namespace Kriterion.DirectDisclosure

open BN254 ArgoMAC

/-- This is the exact missing internal security obligation, not an assumption asserted here. -/
def InternalPrivacy : Prop :=
  ∀ [FieldCertificate] [GroupCertificate],
    GarbledCircuit.ConcreteAdaptivePrivacy (Aux := Unit) internalScheme topology Simulation.simulator
      (Security.randomTape (Seed.randomness 0)) Garbling.oracleHandler Simulation.handler 100

/-- Final wiring is available only when the complete internal100-bit proof is supplied. -/
def solutionOfPrivacy (privacy : InternalPrivacy) : Kriterion.Solution := {
  FixedIndex := Pipeline.FixedKeyIndex
  EncIndex := EncPRF.PermutationIndex
  fixedFinite := inferInstance
  encFinite := inferInstance
  Randomness := Garbling.Randomness
  randomnessFinite := inferInstance
  randomness := Seed.randomness 0
  Public := Public
  EncodingKey := InputMacKey
  State := Simulation.State
  encoding := Wire.encoding
  ciphertextBytes := 40736
  evaluationOracle := fun tape => (tape.fixedKeyOracle, tape.encPRFOracle, tape.hashOracle)
  oracleUniform := by
    convert Security.oracleUniform (Seed.randomness 0) using 1
  scheme := fun field group => @wireScheme field group
  ciphertextSize := by
    intro field group parameter scalar tape
    exact Wire.encoding_length _
  lamportCompatible := fun field group => @wireLamportCompatible field group
  idealOracle := Simulation.handler
  idealView := Simulation.State.view
  functionCorrect := fun _ _ _ _ => rfl
  perfectCorrectness := fun field group => @wirePerfectCorrectness field group
  adaptivePrivacy := by
    intro field group
    letI := field
    letI := group
    let pack := fun labels : Garbling.Labels => Lamport.selectedLabels labels.inputMac
    let restore := fun _ : Nat => ()
    refine ⟨Simulation.simulator.mapLabels pack restore,
      Simulation.oracleSimulation.mapLabels pack restore, ?_⟩
    have internal := @privacy field group
    have wired := internal.mapLabels pack Lamport.restore (fun _ => 40736) restore (fun _ => rfl)
    have instances : (@Fintype.ofFinite Garbling.Randomness inferInstance) =
        Security.garblingRandomnessFintype := Subsingleton.elim _ _
    have tapes : @uniformRandomTape Garbling.Randomness (@Fintype.ofFinite _ inferInstance)
        (Seed.randomness 0) = Security.randomTape (Seed.randomness 0) := by
      unfold uniformRandomTape Security.randomTape
      rw [Cryptography.uniformTape_eq, instances]
    rw [tapes]
    exact wired
}

end Kriterion.DirectDisclosure
