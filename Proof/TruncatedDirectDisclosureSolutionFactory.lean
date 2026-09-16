import Proof.DirectDisclosureSolutionFactory
import Proof.TruncatedDirectDisclosureCorrectness
import Proof.TruncatedDirectDisclosurePrivacy

namespace Kriterion.TruncatedDirectDisclosure
open BN254 ArgoMAC

/-- Complete projected solution, using the original direct-disclosure privacy proof. -/
def solutionForEncoding (encoding : Encoding Public) (bytes : Nat)
    (constant : ∀ table, (encoding.encode table).length = bytes)
    (original : DirectDisclosure.InternalPrivacy) : Kriterion.Solution := {
  FixedIndex := Pipeline.FixedKeyIndex
  EncIndex := EncPRF.PermutationIndex
  fixedFinite := inferInstance
  encFinite := inferInstance
  Randomness := Garbling.Randomness
  randomnessFinite := inferInstance
  randomness := Seed.randomness 0
  Public := Public
  EncodingKey := InputMacKey
  State := DirectDisclosure.Simulation.State
  encoding := encoding
  ciphertextBytes := bytes
  evaluationOracle := fun tape => (tape.fixedKeyOracle, tape.encPRFOracle, tape.hashOracle)
  oracleUniform := by convert Security.oracleUniform (Seed.randomness 0) using 1
  scheme := fun field group => @wireScheme field group
  ciphertextSize := fun _ _ _ _ _ => constant _
  lamportCompatible := fun field group => @wireLamportCompatible field group
  idealOracle := DirectDisclosure.Simulation.handler
  idealView := DirectDisclosure.Simulation.State.view
  functionCorrect := fun _ _ _ _ => rfl
  perfectCorrectness := fun field group => @wirePerfectCorrectness field group
  adaptivePrivacy := by
    intro field group
    letI := field
    letI := group
    let pack := fun labels : Garbling.Labels => Lamport.selectedLabels labels.inputMac
    let restore := fun _ : Nat => ()
    refine ⟨simulator.mapLabels pack restore, oracleSimulation.mapLabels pack restore, ?_⟩
    have privacy := adaptivePrivacy (Security.randomTape (Seed.randomness 0)) (@original field group)
    have wired := privacy.mapLabels pack Lamport.restore (fun _ => bytes) restore (fun _ => rfl)
    have instances : (@Fintype.ofFinite Garbling.Randomness inferInstance) =
        Security.garblingRandomnessFintype := Subsingleton.elim _ _
    have tapes : @uniformRandomTape Garbling.Randomness (@Fintype.ofFinite _ inferInstance)
        (Seed.randomness 0) = Security.randomTape (Seed.randomness 0) := by
      unfold uniformRandomTape Security.randomTape
      rw [Cryptography.uniformTape_eq, instances]
    rw [tapes]
    exact wired
}

/-- The complete 40,419-byte specialization uses the checked universal codec. -/
def solutionOfPrivacy (original : DirectDisclosure.InternalPrivacy) : Kriterion.Solution :=
  solutionForEncoding TruncatedCurveMembership.Wire.encoding 40419
    TruncatedCurveMembership.Wire.encoding_length original

end Kriterion.TruncatedDirectDisclosure
