import Construction.TruncatedDirectDisclosure
import Proof.TruncatedCurveMembership
import Proof.LamportCompatibility.Labels
import Security.Correctness

namespace Kriterion.TruncatedDirectDisclosure
open BN254 ArgoMAC

/-- Projected rows evaluate correctly for every tape and every field input. -/
theorem evaluate_garble [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (tape : Garbling.Randomness) (input : AffineInput) :
    evaluate (tape.fixedKeyOracle, tape.encPRFOracle, tape.hashOracle)
      (TruncatedCurveMembership.project (DirectDisclosure.garble scalar tape)) input
      (tape.inputMacKey.encodeAffine input) = checkedScalarMultiplication scalar input := by
  unfold evaluate checkedScalarMultiplication
  cases decoded : decodePoint input with
  | none => simp only [Option.map_none]
  | some point =>
    have valid : OnCurve input := (decodePoint_defined input).mp (by simp [decoded])
    simp only [DirectDisclosure.garble, Option.map_some]
    rw [TruncatedCurveMembership.evaluate_projected_garble_onCurve _ _ _ _ _ _ _ valid,
      DirectDisclosure.decode_embed]

theorem perfectCorrectness [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.PerfectCorrectness internalScheme
      (fun tape => (tape.fixedKeyOracle, tape.encPRFOracle, tape.hashOracle)) := by
  intro parameter scalar tape input
  simp only [internalScheme, PublicProjection.scheme, DirectDisclosure.internalScheme]
  exact congrArg some (evaluate_garble scalar.value tape input)

theorem wirePerfectCorrectness [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.PerfectCorrectness wireScheme
      (fun tape => (tape.fixedKeyOracle, tape.encPRFOracle, tape.hashOracle)) := by
  intro parameter scalar tape input
  simp only [wireScheme, GarbledCircuit.mapLabels, internalScheme, PublicProjection.scheme,
    DirectDisclosure.internalScheme]
  rw [Lamport.restore_selected]
  exact congrArg some (evaluate_garble scalar.value tape input)

end Kriterion.TruncatedDirectDisclosure
