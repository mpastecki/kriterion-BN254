import Construction.SecureProjectionScheme
import Proof.TruncatedPipeline
import Proof.PublicProjection
import Proof.Privacy
import Proof.LamportCompatibility

namespace Kriterion.ArgoMAC.SecureProjection
open BN254 Cryptography

def wireLamportCompatible [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.LamportCompatibility wireScheme affineLamportBits :=
  PublicProjection.lamportCompatibility Lamport.wireCircuit TruncatedPipeline.project
    evaluateWire affineLamportBits Lamport.compatible

theorem wirePerfectCorrectness [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.PerfectCorrectness wireScheme
      (fun tape => (tape.fixedKeyOracle, tape.encPRFOracle, tape.hashOracle)) := by
  intro parameter scalar tape input
  change some ((TruncatedPipeline.evaluate tape.fixedKeyOracle tape.encPRFOracle tape.hashOracle
      (TruncatedPipeline.project (Garbling.garble construction scalar tape).1)
      (Lamport.restore input (Lamport.selectedLabels (tape.inputMacKey.encodeAffine input))).input
      (Lamport.restore input (Lamport.selectedLabels (tape.inputMacKey.encodeAffine input))).inputMac).bind
      Garbling.decodeResult) = _
  rw [Lamport.restore_selected]
  dsimp only [Garbling.garble]
  rw [TruncatedPipeline.evaluate_projected_garble]
  exact RCBComplete.perfectCorrectness parameter scalar tape input

/-- A complete projected solution inherits E004's output-only simulator and exact oracle game. -/
def solutionForEncoding (encoding : Encoding TruncatedPipeline.Table) (bytes : Nat)
    (constant : ∀ (scalar : NonZeroScalar) (tape : Garbling.Randomness),
      (encoding.encode (TruncatedPipeline.project (Garbling.garble construction scalar tape).1)).length =
        bytes) : Kriterion.Solution := {
  FixedIndex := Pipeline.FixedKeyIndex
  EncIndex := EncPRF.PermutationIndex
  fixedFinite := inferInstance
  encFinite := inferInstance
  Randomness := Garbling.Randomness
  randomnessFinite := inferInstance
  randomness := Seed.randomness 0
  Public := TruncatedPipeline.Table
  EncodingKey := Garbling.EncodingKey
  State := Security.CircuitSimulatorState
  encoding := encoding
  ciphertextBytes := bytes
  evaluationOracle := fun tape => (tape.fixedKeyOracle, tape.encPRFOracle, tape.hashOracle)
  oracleUniform := by convert Security.oracleUniform (Seed.randomness 0) using 1
  scheme := fun field group => @wireScheme field group
  ciphertextSize := fun _ _ _ scalar tape => constant scalar tape
  lamportCompatible := fun field group => @wireLamportCompatible field group
  idealOracle := Security.circuitSimulatorOracleHandler
  idealView := Security.CircuitSimulatorState.view
  functionCorrect := fun _ _ _ _ => rfl
  perfectCorrectness := fun field group => @wirePerfectCorrectness field group
  adaptivePrivacy := by
    intro field group
    letI := field
    letI := group
    let pack := fun labels : Garbling.Labels => Lamport.selectedLabels labels.inputMac
    let restore := fun _ : Nat => (⟨508, 91⟩ : Garbling.Topology)
    let originalSimulator := Security.concreteCircuitSimulator.mapLabels pack restore
    refine ⟨PublicProjection.simulator originalSimulator TruncatedPipeline.project,
      PublicProjection.oracleSimulation originalSimulator TruncatedPipeline.project
        Security.circuitSimulatorOracleHandler Security.CircuitSimulatorState.view
        (Security.concreteCircuitSimulator_rules.mapLabels pack restore), ?_⟩
    have originalPrivacy :=
      (Security.concreteAdaptivePrivacy (Aux := Unit) (Seed.randomness 0)).mapLabels
        pack Lamport.restore (fun _ => bytes) restore (fun _ => rfl)
    have privacy := PublicProjection.adaptivePrivacy Lamport.wireCircuit TruncatedPipeline.project
      evaluateWire (fun _ => bytes) originalSimulator (Security.randomTape (Seed.randomness 0))
      Garbling.oracleHandler Security.circuitSimulatorOracleHandler 100 originalPrivacy
    have instances : (@Fintype.ofFinite Garbling.Randomness inferInstance) =
        Security.garblingRandomnessFintype := Subsingleton.elim _ _
    have tapes : @uniformRandomTape Garbling.Randomness (@Fintype.ofFinite _ inferInstance)
        (Seed.randomness 0) = Security.randomTape (Seed.randomness 0) := by
      unfold uniformRandomTape Security.randomTape
      rw [Cryptography.uniformTape_eq, instances]
    rw [tapes]
    exact privacy
}

end Kriterion.ArgoMAC.SecureProjection
