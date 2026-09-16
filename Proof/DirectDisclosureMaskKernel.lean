import Proof.DirectDisclosureSourceKernel

namespace Kriterion.DirectDisclosure.SourceKernel

open BN254 Cryptography ArgoMAC ArgoMAC.Security
noncomputable section
attribute [local instance] bitAdaptorTableFintype publicVectorFintype ciphertextFintype curveMaskSampleFintype
local instance : Nonempty CurvePublicSample := ⟨defaultSimulatorCoin.tableSample.curve⟩
local instance : Nonempty CurveMaskSample :=
  ⟨((fun _ => 0, fun _ _ => 0),
    (fun _ => Vector.replicate coordinateBitCount defaultBitAdaptorTable),
    fun _ _ => defaultHashLiftQuotient)⟩

def masked {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (scalar : ScalarField) (auxiliary : Aux)
    (mask : BaseField) (source : CurveMaskSample) (oracles : SimulatorOracleCoin) (key : InputMacKey) :
    PMF (Transcript adversary.State) :=
  run adversary parameter auxiliary
    (ConditionalDisclosure.CurveSource.sourceTable (embedScalar scalar) mask source) oracles key fun input =>
      (curveMaskSampleGarble (embedScalar scalar) mask input source).request

private theorem target_order [FieldCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (scalar : ScalarField) (auxiliary : Aux)
    (sample : CurvePublicSample) (oracles : SimulatorOracleCoin) (key : InputMacKey) :
    (PMF.uniformOfFintype BaseField).bind (fun target =>
      ideal adversary parameter scalar auxiliary ⟨sample, oracles, key, target⟩) =
    (choose adversary parameter auxiliary sample.request.table oracles).bind fun choice =>
      (PMF.uniformOfFintype BaseField).bind fun target =>
        observe adversary parameter auxiliary key choice
          (sample.request.retarget choice.1 (MaskSource.selectedTarget (embedScalar scalar) choice.1 target)) := by
  unfold ideal run
  exact PMF.bind_comm (PMF.uniformOfFintype BaseField)
    (choose adversary parameter auxiliary sample.request.table oracles)
    (fun target choice => observe adversary parameter auxiliary key choice
      (sample.request.retarget choice.1 (MaskSource.selectedTarget (embedScalar scalar) choice.1 target)))

/-- Fixed-bridge mask transport is applied to the complete two-phase transcript
kernel: public table, chosen adversary state, labels, both oracle histories and decision.
It therefore handles adaptive inputs and post-label queries, not only selected outputs. -/
theorem mask_kernel_bound [FieldCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (scalar : ScalarField) (auxiliary : Aux)
    (oracles : SimulatorOracleCoin) (key : InputMacKey) (event : Set (Transcript adversary.State)) :
    |(((PMF.uniformOfFintype CurvePublicSample).bind fun sample =>
        (PMF.uniformOfFintype BaseField).bind fun target =>
          ideal adversary parameter scalar auxiliary ⟨sample, oracles, key, target⟩).toOuterMeasure event).toReal -
      (((PMF.uniformOfFintype NonZeroBase).bind fun mask =>
        (PMF.uniformOfFintype CurveMaskSample).bind fun source =>
          masked adversary parameter scalar auxiliary mask.value source oracles key).toOuterMeasure event).toReal| ≤
      1 / (baseFieldModulus : ℝ) := by
  have bound := MaskSource.adaptive_nonzero_mask_observation_bound (embedScalar scalar)
    (fun table => choose adversary parameter auxiliary table oracles)
    (fun choice mask _ source => observe adversary parameter auxiliary key choice
      (curveMaskSampleGarble (embedScalar scalar) mask choice.1 source).request) event
  simp only [MaskSource.reindexed_request] at bound
  simpa only [target_order, masked, run] using bound

end
end Kriterion.DirectDisclosure.SourceKernel
