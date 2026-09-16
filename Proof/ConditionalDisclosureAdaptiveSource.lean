import Proof.ConditionalDisclosureCurve
import Proof.Privacy.Distribution.AdaptiveMaskDistribution

namespace Kriterion.ConditionalDisclosure.CurveSource

open BN254 Cryptography ArgoMAC ArgoMAC.Security
noncomputable section

attribute [local instance] bitAdaptorTableFintype publicVectorFintype ciphertextFintype
  curveMaskSampleFintype

local instance : Nonempty CurvePublicSample := ⟨defaultSimulatorCoin.tableSample.curve⟩
local instance : Nonempty CurveMaskSample :=
  ⟨((fun _ => 0, fun _ _ => 0),
    (fun _ => Vector.replicate coordinateBitCount defaultBitAdaptorTable),
    fun _ _ => defaultHashLiftQuotient)⟩

private theorem sample_result (sample : CurvePublicSample) (input : AffineInput) :
    curveMaskResult input (curveSampleViewEquiv sample).1 = sample.request.result input := by
  simp [curveMaskResult, curveMaskRest, curveSampleViewEquiv, CurvePublicSample.request,
    CurveGateRequest.result]
  ring

private theorem sample_pivot (sample : CurvePublicSample)
    (input : AffineInput) (target : BaseField) :
    curveSampleViewEquiv.symm (curveMaskPivot (target - curveMaskResult input (curveSampleViewEquiv sample).1)
      (curveSampleViewEquiv sample).1, (curveSampleViewEquiv sample).2) = sample.retargetMask input target := by
  rw [sample_result]
  unfold curveMaskPivot curveSampleViewEquiv CurvePublicSample.retargetMask
  dsimp
  rw [lowMaskShift_eq_retargetBits]
  rw [add_comm (DigitAdaptor.fromBits _) (target - sample.request.result input)]

theorem garble_split (bridge mask : BaseField) (input : AffineInput)
    (sample : CurvePublicSample) :
    curveMaskSampleGarble bridge mask input (curveMaskSampleSplit bridge mask input sample).2 =
      sample.retargetMask input (bridge + mask * (input.x ^ 3 + 3 - input.y ^ 2)) := by
  unfold curveMaskSampleGarble curveMaskSampleSplit
  rw [maskSampleSplitEquiv_selected]
  exact sample_pivot sample input _

set_option maxRecDepth 10000 in
/-- The actual source publishes one curve table independently of the later selected input. -/
theorem garble_table_input (bridge mask : BaseField) (source : CurveMaskSample)
    (first second : AffineInput) :
    (curveMaskSampleGarble bridge mask first source).request.table =
      (curveMaskSampleGarble bridge mask second source).request.table := by
  have coefficients : (curveMaskViewEquiv bridge mask first source.1).1.1 =
      (curveMaskViewEquiv bridge mask second source.1).1.1 := by
    funext index
    refine Fin.cases ?_ ?_ index
    · rw [curveMaskViewEquiv_constant, curveMaskViewEquiv_constant]
    · intro index
      have tail (input : AffineInput) := congrArg (fun data : CurveMaskData => data.1 index)
        ((curveMaskFiberEquiv input (bridge + mask * (input.x ^ 3 + 3 - input.y ^ 2))).symm_apply_apply
          (curveMaskShiftEquiv mask input source.1))
      exact (tail first).trans (tail second).symm
  dsimp only [curveMaskSampleGarble, curveSampleViewEquiv, Equiv.symm, Equiv.coe_fn_mk,
    CurvePublicSample.request, CurveGateRequest.table]
  rw [coefficients]

def sourceTable (bridge mask : BaseField) (source : CurveMaskSample) : CurveMembership.Table :=
  (curveMaskSampleGarble bridge mask ⟨0, 0⟩ source).request.table

theorem sourceTable_actual (bridge mask r1 r2 : BaseField)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) (inputKey : InputMacKey)
    (quotients : Fin 5 → Fin coordinateBitCount → HashLiftQuotient) :
    sourceTable bridge mask (maskSource bridge mask r1 r2 oracle inputKey quotients) =
      CurveMembership.garble bridge mask r1 r2 (Pipeline.curveOracles oracle) inputKey :=
  actualCurveMaskSample_table bridge mask r1 r2 (Pipeline.curveOracles oracle) inputKey quotients ⟨0, 0⟩

theorem split_table (bridge mask : BaseField) (input : AffineInput) (sample : CurvePublicSample) :
    sourceTable bridge mask (curveMaskSampleSplit bridge mask input sample).2 = sample.request.table := by
  unfold sourceTable
  rw [garble_table_input bridge mask _ ⟨0, 0⟩ input, garble_split,
    CurvePublicSample.retargetMask_request, CurveGateRequest.retarget_table]

/-- The complete public view includes the committed scalar ciphertext. -/
def publicView (ciphertext : Ciphertext) (sample : CurvePublicSample) : Public :=
  ⟨sample.request.table, ciphertext⟩

def sourceView (bridge mask : BaseField) (ciphertext : Ciphertext) (source : CurveMaskSample) : Public :=
  ⟨sourceTable bridge mask source, ciphertext⟩

/-- Arbitrary randomized input choice can retain all prefix state/transcript data in Aux.
This is an exact preserved-public-view source law, not a fixed-input marginal. -/
theorem adaptive_split_uniform {Aux : Type*} (bridge mask : BaseField) (ciphertext : Ciphertext)
    (choose : Public → PMF (AffineInput × Aux)) :
    (PMF.uniformOfFintype CurvePublicSample).bind (fun sample =>
      (choose (publicView ciphertext sample)).map (fun selected =>
        (selected, (curveMaskSampleSplit bridge mask selected.1 sample).2))) =
    (PMF.uniformOfFintype CurveMaskSample).bind (fun source =>
      (choose (sourceView bridge mask ciphertext source)).map (fun selected => (selected, source))) := by
  have same := uniform_bind_viewEquiv
    (fun selected : AffineInput × Aux => curveMaskSampleSplit bridge mask selected.1)
    (publicView ciphertext) (fun pair => sourceView bridge mask ciphertext pair.2)
    (fun selected sample => congrArg (fun value => (⟨value, ciphertext⟩ : Public))
      (split_table bridge mask selected.1 sample)) choose
  have projected := congrArg (fun distribution => distribution.map
    (fun pair : (AffineInput × Aux) × (BaseField × CurveMaskSample) => (pair.1, pair.2.2))) same
  simp only [PMF.map_bind, PMF.map_comp] at projected
  change _ = (PMF.uniformOfFintype (BaseField × CurveMaskSample)).bind
    ((fun source => (choose (sourceView bridge mask ciphertext source)).map
      (fun selected => (selected, source))) ∘ Prod.snd) at projected
  rw [← PMF.bind_map, map_uniform_prod_snd] at projected
  exact projected

/-- The source comparison retains every curve mask and quotient for the later
permutation count, while letting the adversary adapt to both public components. -/
theorem adaptive_retained_observation {Aux Observation : Type*}
    (bridge mask : BaseField) (ciphertext : Ciphertext)
    (choose : Public → PMF (AffineInput × Aux))
    (observe : (AffineInput × Aux) → CurveMaskSample → PMF Observation) :
    (PMF.uniformOfFintype CurveMaskSample).bind (fun source =>
      (choose (sourceView bridge mask ciphertext source)).bind fun selected => observe selected source) =
    (PMF.uniformOfFintype CurvePublicSample).bind (fun sample =>
      (choose (publicView ciphertext sample)).bind fun selected =>
        observe selected (curveMaskSampleSplit bridge mask selected.1 sample).2) := by
  have law := congrArg (fun distribution => distribution.bind
    (fun pair : (AffineInput × Aux) × CurveMaskSample => observe pair.1 pair.2))
    (adaptive_split_uniform bridge mask ciphertext choose)
  simp only [PMF.bind_bind, PMF.bind_map] at law
  exact law.symm

/-- In the selected program, the actual source request equals the simulator's
retargeted request, preserving its full public table. -/
theorem adaptive_request_law {Aux : Type*}
    (bridge mask : BaseField) (ciphertext : Ciphertext)
    (choose : Public → PMF (AffineInput × Aux)) :
    (PMF.uniformOfFintype CurveMaskSample).bind (fun source =>
      (choose (sourceView bridge mask ciphertext source)).map (fun selected =>
        (selected, (curveMaskSampleGarble bridge mask selected.1 source).request))) =
    (PMF.uniformOfFintype CurvePublicSample).bind (fun sample =>
      (choose (publicView ciphertext sample)).map (fun selected =>
        (selected, sample.request.retarget selected.1
          (bridge + mask * (selected.1.x ^ 3 + 3 - selected.1.y ^ 2))))) := by
  have same := congrArg (fun distribution => distribution.map
    (fun pair : (AffineInput × Aux) × CurveMaskSample =>
      (pair.1, (curveMaskSampleGarble bridge mask pair.1.1 pair.2).request)))
    (adaptive_split_uniform bridge mask ciphertext choose)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, garble_split,
    CurvePublicSample.retargetMask_request] at same
  exact same.symm

end
end Kriterion.ConditionalDisclosure.CurveSource
