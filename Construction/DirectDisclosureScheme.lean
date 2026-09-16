import Construction.DirectDisclosureEncoding

namespace Kriterion.DirectDisclosure

open BN254 ArgoMAC

abbrev Randomness := ArgoMAC.Garbling.Randomness
abbrev EncodingKey := InputMacKey
abbrev Labels := ArgoMAC.Garbling.Labels
abbrev Oracle := ArgoMAC.Garbling.EvaluationOracle

/-- The CDS public topology does not depend on the secret scalar. -/
def topology (_ : NonZeroScalar) : Unit := ()

/-- Internal-label conditional disclosure circuit. -/
def internalScheme [FieldCertificate] [GroupCertificate] :
    GarbledCircuit NonZeroScalar AffineInput (Option Point) Randomness Public
      EncodingKey Labels Oracle where
  function := fun scalar input => checkedScalarMultiplication scalar.value input
  garble := fun _ scalar tape => (garble scalar.value tape, tape.inputMacKey)
  encode := fun key input => {
    input := BitInput.ofAffine input
    inputMac := key.encodeAffine input
  }
  evaluate := fun oracle table input labels => some (evaluate oracle table input labels.inputMac)

/-- The external evaluator receives exactly the 508 selected Lamport blocks. -/
def wireScheme [FieldCertificate] [GroupCertificate] :
    GarbledCircuit NonZeroScalar AffineInput (Option Point) Randomness Public
      EncodingKey GarbledCircuit.LamportSignature Oracle :=
  internalScheme.mapLabels (fun labels => ArgoMAC.Lamport.selectedLabels labels.inputMac)
    ArgoMAC.Lamport.restore

end Kriterion.DirectDisclosure
