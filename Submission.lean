import Solution
import Construction
import Proof

namespace Submission
open Kriterion Kriterion.BN254 Kriterion.ArgoMAC

/-- The scalar-hiding ArgoMAC garbling with every public row projected to 254 bits. -/
def solution : Kriterion.Solution :=
  SecureProjection.solutionForEncoding
    (TruncatedPipeline.Wire.encoding TruncatedCurveMembership.JointWire.encoding) 8887256
    (TruncatedPipeline.Wire.garble_length TruncatedCurveMembership.JointWire.encoding 40418
      TruncatedCurveMembership.JointWire.encoding_length construction)

end Submission
