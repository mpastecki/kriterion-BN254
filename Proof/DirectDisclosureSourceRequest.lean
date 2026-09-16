import Proof.DirectDisclosureMaskSource
import Proof.DirectDisclosureSimulator

namespace Kriterion.DirectDisclosure.Simulation

open BN254 Cryptography ArgoMAC ArgoMAC.Security
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The permitted output reconstructs exactly the fixed embedded scalar on valid
inputs; the invalid branch uses only the simulator's independent target. -/
theorem selectedTarget_real [FieldCertificate] [GroupCertificate]
    (state : State) (scalar : ScalarField) (input : AffineInput) :
    state.selectedTarget input (checkedScalarMultiplication scalar input) =
      MaskSource.selectedTarget (embedScalar scalar) input state.target := by
  by_cases valid : OnCurve input
  · simp only [State.selectedTarget, MaskSource.selectedTarget, if_pos valid,
      ScalarRecovery.recover_correct scalar input valid]
  · simp only [State.selectedTarget, MaskSource.selectedTarget, if_neg valid]

/-- The actual source reconstructed by the fixed-bridge transport has exactly the
selected simulator request. No equality of source distributions is assumed here. -/
theorem reconstructed_request [FieldCertificate] [GroupCertificate]
    (coin : Coin) (scalar : ScalarField) (input : AffineInput) :
    let mask := (MaskSource.maskEquiv (embedScalar scalar) input).symm coin.target
    (curveMaskSampleGarble (embedScalar scalar) mask input
      (curveMaskSampleSplit (embedScalar scalar) mask input coin.curve).2).request =
      coin.state.selectedCurve input (checkedScalarMultiplication scalar input) := by
  dsimp only
  rw [MaskSource.reindexed_request]
  simp only [State.selectedCurve, selectedTarget_real, Coin.state]

end
end Kriterion.DirectDisclosure.Simulation
