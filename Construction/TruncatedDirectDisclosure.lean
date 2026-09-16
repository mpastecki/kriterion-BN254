import Construction.DirectDisclosureScheme
import Construction.TruncatedCurveEncoding
import Construction.PublicProjection

namespace Kriterion.TruncatedDirectDisclosure
open BN254 ArgoMAC

abbrev Public := TruncatedCurveMembership.Table

/-- The evaluator uses the selected label to remove the truncated pad. -/
def evaluate [FieldCertificate] [GroupCertificate]
    (oracle : Garbling.EvaluationOracle) (table : Public) (input : AffineInput)
    (labels : InputMac) : Option Point :=
  (decodePoint input).map fun point =>
    scalarMultiplication (DirectDisclosure.decodeScalar
      (TruncatedCurveMembership.evaluate oracle.1 table input labels)) point

/-- The original garbler and encoding key are retained; only public rows are projected. -/
def internalScheme [FieldCertificate] [GroupCertificate] :
    GarbledCircuit NonZeroScalar AffineInput (Option Point) Garbling.Randomness Public
      InputMacKey Garbling.Labels Garbling.EvaluationOracle :=
  PublicProjection.scheme DirectDisclosure.internalScheme TruncatedCurveMembership.project
    (fun oracle table input labels => some (evaluate oracle table input labels.inputMac))

def wireScheme [FieldCertificate] [GroupCertificate] :
    GarbledCircuit NonZeroScalar AffineInput (Option Point) Garbling.Randomness Public
      InputMacKey GarbledCircuit.LamportSignature Garbling.EvaluationOracle :=
  internalScheme.mapLabels (fun labels => Lamport.selectedLabels labels.inputMac) Lamport.restore

def topology : NonZeroScalar → Unit := DirectDisclosure.topology

end Kriterion.TruncatedDirectDisclosure
