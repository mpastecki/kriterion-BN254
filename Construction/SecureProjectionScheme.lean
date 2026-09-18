import Construction.PublicProjection
import Construction.TruncatedPipeline
import Construction.Garbling

namespace Kriterion.ArgoMAC.SecureProjection
open BN254 Cryptography

def evaluateWire [FieldCertificate] [GroupCertificate]
    (oracle : Garbling.EvaluationOracle) (table : TruncatedPipeline.Table)
    (input : AffineInput) (labels : GarbledCircuit.LamportSignature) : Option (Option Point) :=
  let restored := Lamport.restore input labels
  some ((TruncatedPipeline.evaluate oracle.1 oracle.2.1 oracle.2.2
    table restored.input restored.inputMac).bind Garbling.decodeResult)

/-- Only the public table changes; the original scalar-hiding garbling and labels remain. -/
def wireScheme [FieldCertificate] [GroupCertificate] :=
  PublicProjection.scheme Lamport.wireCircuit TruncatedPipeline.project evaluateWire

end Kriterion.ArgoMAC.SecureProjection
