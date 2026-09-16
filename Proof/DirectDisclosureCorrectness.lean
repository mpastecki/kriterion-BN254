import Construction.DirectDisclosureScheme
import Proof.LamportCompatibility.Labels
import Security.Correctness

namespace Kriterion.DirectDisclosure

open BN254 ArgoMAC

theorem functionCorrect [FieldCertificate] [GroupCertificate]
    (scalar : NonZeroScalar) (input : AffineInput) :
    (internalScheme.function scalar input) = checkedScalarMultiplication scalar.value input := rfl

theorem perfectCorrectness [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.PerfectCorrectness internalScheme
      (fun tape => (tape.fixedKeyOracle, tape.encPRFOracle, tape.hashOracle)) := by
  intro parameter scalar tape input
  simp only [internalScheme]
  exact congrArg some (evaluate_garble scalar.value tape input)

theorem wirePerfectCorrectness [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.PerfectCorrectness wireScheme
      (fun tape => (tape.fixedKeyOracle, tape.encPRFOracle, tape.hashOracle)) := by
  intro parameter scalar tape input
  simp only [wireScheme, GarbledCircuit.mapLabels, internalScheme]
  rw [ArgoMAC.Lamport.restore_selected]
  exact congrArg some (evaluate_garble scalar.value tape input)

def wireLamportCompatible [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.LamportCompatibility wireScheme affineLamportBits := {
  keyPairs := fun key => ArgoMAC.Lamport.keyPairs key
  encodeSelectsLabels := by
    intro key input
    exact ArgoMAC.Lamport.selectedLabels_eq key input
}

theorem ciphertextSize [FieldCertificate] [GroupCertificate]
    (scalar : NonZeroScalar) (tape : Randomness) :
    (Wire.encoding.encode (internalScheme.garble 0 scalar tape).1).length = 40736 := by
  exact Wire.encoding_length _

end Kriterion.DirectDisclosure
