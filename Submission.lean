import Solution
import Construction
import Proof

namespace Submission

/-- Complete curve-gated scalar disclosure with truncated public rows. -/
def solution : Kriterion.Solution :=
  Kriterion.TruncatedDirectDisclosure.solutionForEncoding
    Kriterion.ArgoMAC.TruncatedCurveMembership.JointWire.encoding 40418
    Kriterion.ArgoMAC.TruncatedCurveMembership.JointWire.encoding_length (by
    intro field group
    exact @Kriterion.DirectDisclosure.adaptivePrivacy field group Unit
      (Kriterion.ArgoMAC.Seed.randomness 0))

end Submission
