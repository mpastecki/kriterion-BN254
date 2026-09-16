import Proof.ConditionalDisclosureAdaptiveSource
import Proof.Privacy.Distribution.OffCurveDistribution

namespace Kriterion.DirectDisclosure.MaskSource

open BN254 Cryptography ArgoMAC ArgoMAC.Security
noncomputable section
attribute [local instance] Classical.propDecidable
  bitAdaptorTableFintype publicVectorFintype ciphertextFintype curveMaskSampleFintype
local instance : Nonempty CurvePublicSample := ⟨defaultSimulatorCoin.tableSample.curve⟩
local instance : Nonempty CurveMaskSample :=
  ⟨((fun _ => 0, fun _ _ => 0),
    (fun _ => Vector.replicate coordinateBitCount defaultBitAdaptorTable),
    fun _ _ => defaultHashLiftQuotient)⟩

/-- The bridge is fixed. Only the mask is reindexed; the valid branch keeps it. -/
def maskEquiv [FieldCertificate] (bridge : BaseField) (input : AffineInput) :
    BaseField ≃ BaseField :=
  if valid : OnCurve input then Equiv.refl _ else
  { toFun := fun mask => bridge + mask * (input.x ^ 3 + 3 - input.y ^ 2)
    invFun := fun target => (target - bridge) / (input.x ^ 3 + 3 - input.y ^ 2)
    left_inv := fun mask => by
      dsimp
      rw [add_sub_cancel_left, mul_div_cancel_right₀ _ (curveResidual_ne_zero input valid)]
    right_inv := fun target => by
      dsimp
      rw [div_mul_cancel₀ _ (curveResidual_ne_zero input valid)]
      ring }

def selectedTarget (bridge : BaseField) (input : AffineInput) (target : BaseField) : BaseField :=
  if OnCurve input then bridge else target

theorem selectedTarget_maskEquiv [FieldCertificate]
    (bridge : BaseField) (input : AffineInput) (mask : BaseField) :
    selectedTarget bridge input (maskEquiv bridge input mask) =
      bridge + mask * (input.x ^ 3 + 3 - input.y ^ 2) := by
  by_cases valid : OnCurve input
  · have residual : input.x ^ 3 + 3 - input.y ^ 2 = 0 := sub_eq_zero.mpr valid.symm
    simp [selectedTarget, valid, residual]
  · simp [selectedTarget, maskEquiv, valid]

/-- Reconstructing the complete source produces exactly the simulator's selected
curve request, for valid and invalid inputs and every sampled field target. -/
theorem reindexed_request [FieldCertificate]
    (bridge : BaseField) (input : AffineInput) (target : BaseField) (sample : CurvePublicSample) :
    (curveMaskSampleGarble bridge ((maskEquiv bridge input).symm target) input
      (curveMaskSampleSplit bridge ((maskEquiv bridge input).symm target) input sample).2).request =
      sample.request.retarget input (selectedTarget bridge input target) := by
  rw [ConditionalDisclosure.CurveSource.garble_split, CurvePublicSample.retargetMask_request]
  have result := selectedTarget_maskEquiv bridge input ((maskEquiv bridge input).symm target)
  rw [Equiv.apply_symm_apply] at result
  rw [← result]

/-- Every original private curve field is retained in the observer. This is not a
marginal law of the selected output, and the bridge is never sampled here. -/
theorem full_mask_transport [FieldCertificate] {Aux Observation : Type*}
    (bridge : BaseField) (selected : PMF (AffineInput × Aux))
    (sample : (AffineInput × Aux) → CurvePublicSample)
    (observe : (AffineInput × Aux) → BaseField → BaseField → CurveMaskSample → PMF Observation) :
    (selected.bind fun choice => (PMF.uniformOfFintype BaseField).bind fun mask =>
      observe choice mask (bridge + mask * (choice.1.x ^ 3 + 3 - choice.1.y ^ 2))
        (curveMaskSampleSplit bridge mask choice.1 (sample choice)).2) =
    (selected.bind fun choice => (PMF.uniformOfFintype BaseField).bind fun target =>
      let mask := (maskEquiv bridge choice.1).symm target
      observe choice mask (selectedTarget bridge choice.1 target)
        (curveMaskSampleSplit bridge mask choice.1 (sample choice)).2) := by
  apply congrArg (selected.bind)
  funext choice
  have uniform := map_uniformOfFintype_equivBetween (maskEquiv bridge choice.1)
  conv_rhs => rw [← uniform, PMF.bind_map]
  simp only [Function.comp_def, Equiv.symm_apply_apply, selectedTarget_maskEquiv]

/-- The original nonzero mask and the fixed-bridge reindexed full source differ
by at most 1/p for every event after arbitrary selected-input and retained-state observation. -/
theorem nonzero_mask_observation_bound [FieldCertificate] {Aux Observation : Type*}
    (bridge : BaseField) (selected : PMF (AffineInput × Aux))
    (sample : (AffineInput × Aux) → CurvePublicSample)
    (observe : (AffineInput × Aux) → BaseField → BaseField → CurveMaskSample → PMF Observation)
    (event : Set Observation) :
    |((selected.bind fun choice => (PMF.uniformOfFintype BaseField).bind fun target =>
        let mask := (maskEquiv bridge choice.1).symm target
        observe choice mask (selectedTarget bridge choice.1 target)
          (curveMaskSampleSplit bridge mask choice.1 (sample choice)).2).toOuterMeasure event).toReal -
      ((selected.bind fun choice => (PMF.uniformOfFintype NonZeroBase).bind fun mask =>
        observe choice mask.value (bridge + mask.value * (choice.1.x ^ 3 + 3 - choice.1.y ^ 2))
          (curveMaskSampleSplit bridge mask.value choice.1 (sample choice)).2).toOuterMeasure event).toReal| ≤
      1 / (baseFieldModulus : ℝ) := by
  rw [← full_mask_transport]
  rw [PMF.bind_comm selected (PMF.uniformOfFintype BaseField),
    PMF.bind_comm selected (PMF.uniformOfFintype NonZeroBase)]
  exact curveMask_observation_bound (fun mask => selected.bind fun choice =>
    observe choice mask (bridge + mask * (choice.1.x ^ 3 + 3 - choice.1.y ^ 2))
      (curveMaskSampleSplit bridge mask choice.1 (sample choice)).2) event

/-- The preserved public view permits arbitrary adaptive choice before the fixed-bridge
mask transport, retaining all source rows, quotients, and any auxiliary transcript. -/
theorem adaptive_retained_observation {Aux Observation : Type*}
    (bridge mask : BaseField)
    (choose : CurveMembership.Table → PMF (AffineInput × Aux))
    (observe : (AffineInput × Aux) → CurveMaskSample → PMF Observation) :
    (PMF.uniformOfFintype CurveMaskSample).bind (fun source =>
      (choose (ConditionalDisclosure.CurveSource.sourceTable bridge mask source)).bind
        fun selected => observe selected source) =
    (PMF.uniformOfFintype CurvePublicSample).bind (fun sample =>
      (choose sample.request.table).bind fun selected =>
        observe selected (curveMaskSampleSplit bridge mask selected.1 sample).2) :=
  ConditionalDisclosure.CurveSource.adaptive_retained_observation bridge mask 0
    (fun value => choose value.curve) observe

/-- Full fixed-bridge transport in the actual order: publish the source table, let
an arbitrary randomized adversary choose its input, and retain its complete state.
The right side samples the target after that choice; no input-independence premise is used. -/
theorem adaptive_full_mask_transport [FieldCertificate] {Aux Observation : Type*}
    (bridge : BaseField) (choose : CurveMembership.Table → PMF (AffineInput × Aux))
    (observe : (AffineInput × Aux) → BaseField → BaseField → CurveMaskSample → PMF Observation) :
    ((PMF.uniformOfFintype BaseField).bind fun mask =>
      (PMF.uniformOfFintype CurveMaskSample).bind fun source =>
        (choose (ConditionalDisclosure.CurveSource.sourceTable bridge mask source)).bind fun choice =>
          observe choice mask (bridge + mask * (choice.1.x ^ 3 + 3 - choice.1.y ^ 2)) source) =
    ((PMF.uniformOfFintype CurvePublicSample).bind fun sample =>
      (choose sample.request.table).bind fun choice =>
        (PMF.uniformOfFintype BaseField).bind fun target =>
          let mask := (maskEquiv bridge choice.1).symm target
          observe choice mask (selectedTarget bridge choice.1 target)
            (curveMaskSampleSplit bridge mask choice.1 sample).2) := by
  simp_rw [adaptive_retained_observation]
  rw [PMF.bind_comm (PMF.uniformOfFintype BaseField) (PMF.uniformOfFintype CurvePublicSample)]
  apply congrArg ((PMF.uniformOfFintype CurvePublicSample).bind)
  funext sample
  rw [PMF.bind_comm (PMF.uniformOfFintype BaseField) (choose sample.request.table)]
  exact full_mask_transport bridge (choose sample.request.table) (fun _ => sample) observe

/-- The same complete adaptive law for the actual nonzero mask, with the sole
mask-conditioning loss bounded by 1/p. All permutation/hash source losses remain separate. -/
theorem adaptive_nonzero_mask_observation_bound [FieldCertificate] {Aux Observation : Type*}
    (bridge : BaseField) (choose : CurveMembership.Table → PMF (AffineInput × Aux))
    (observe : (AffineInput × Aux) → BaseField → BaseField → CurveMaskSample → PMF Observation)
    (event : Set Observation) :
    |(((PMF.uniformOfFintype CurvePublicSample).bind fun sample =>
        (choose sample.request.table).bind fun choice =>
          (PMF.uniformOfFintype BaseField).bind fun target =>
            let mask := (maskEquiv bridge choice.1).symm target
            observe choice mask (selectedTarget bridge choice.1 target)
              (curveMaskSampleSplit bridge mask choice.1 sample).2).toOuterMeasure event).toReal -
      (((PMF.uniformOfFintype NonZeroBase).bind fun mask =>
        (PMF.uniformOfFintype CurveMaskSample).bind fun source =>
          (choose (ConditionalDisclosure.CurveSource.sourceTable bridge mask.value source)).bind fun choice =>
            observe choice mask.value
              (bridge + mask.value * (choice.1.x ^ 3 + 3 - choice.1.y ^ 2)) source).toOuterMeasure event).toReal| ≤
      1 / (baseFieldModulus : ℝ) := by
  rw [← adaptive_full_mask_transport]
  exact curveMask_observation_bound (fun mask =>
    (PMF.uniformOfFintype CurveMaskSample).bind fun source =>
      (choose (ConditionalDisclosure.CurveSource.sourceTable bridge mask source)).bind fun choice =>
        observe choice mask (bridge + mask * (choice.1.x ^ 3 + 3 - choice.1.y ^ 2)) source) event

end
end Kriterion.DirectDisclosure.MaskSource
