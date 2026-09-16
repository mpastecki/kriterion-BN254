import Proof.ConditionalDisclosureCurve
import Proof.Privacy.Programming.ActualScheduleRecords

namespace Kriterion.ConditionalDisclosure

open BN254 Cryptography ArgoMAC ArgoMAC.Security

private def curveLifts (source : CurveMaskSample) : CurveSource.Gate → FullHashLift :=
  fun gate => goodHashLiftSource (CurveSource.field source gate, source.2.2 gate.1 gate.2)

private def curveRequest (bridge mask : BaseField) (input : AffineInput)
    (source : CurveMaskSample) : CurveGateRequest :=
  (curveMaskSampleGarble bridge mask input source).request

private def curveDirective (bridge mask : BaseField) (input : AffineInput)
    (source : CurveMaskSample) (inputKey : InputMacKey) (gate : CurveSource.Gate) : GateDirective :=
  (curveRequest bridge mask input source).actualDirective input (inputKey.encodeAffine input) gate.1 gate.2

private theorem curveDirective_location (bridge mask : BaseField) (input : AffineInput)
    (source : CurveMaskSample) (inputKey : InputMacKey) (gate : CurveSource.Gate) :
    (curveDirective bridge mask input source inputKey gate).location = CurveSource.location gate := by
  rcases gate with ⟨adaptor, bit⟩
  fin_cases adaptor <;> rfl

private theorem curveDirective_window (bridge mask : BaseField) (input : AffineInput)
    (source : CurveMaskSample) (inputKey : InputMacKey) (gate : CurveSource.Gate) :
    (curveDirective bridge mask input source inputKey gate).window = gate.2.val := by
  rcases gate with ⟨adaptor, bit⟩
  fin_cases adaptor <;> rfl

private theorem curveDirective_label (bridge mask : BaseField) (input : AffineInput)
    (source : CurveMaskSample) (inputKey : InputMacKey) (gate : CurveSource.Gate) :
    (curveDirective bridge mask input source inputKey gate).label =
      BitAdaptor.encode (CurveSource.key inputKey gate)
        (curveDirective bridge mask input source inputKey gate).bit := by
  rcases gate with ⟨adaptor, bit⟩
  fin_cases adaptor <;>
    simp [curveDirective, curveRequest, CurveGateRequest.actualDirective, actualDigitDirective,
      CurveSource.key, InputMacKey.encodeAffine, InputMacKey.encode, BitInput.ofAffine,
      encodeCoordinate, coordinateValues] <;> rfl

private theorem curveDirective_table (bridge mask : BaseField) (input : AffineInput)
    (source : CurveMaskSample) (inputKey : InputMacKey) (gate : CurveSource.Gate) :
    (curveDirective bridge mask input source inputKey gate).table = CurveSource.table source gate := by
  rcases gate with ⟨adaptor, bit⟩
  fin_cases adaptor <;> rfl

private theorem curveDirective_target (bridge mask : BaseField) (input : AffineInput)
    (source : CurveMaskSample) (inputKey : InputMacKey) (gate : CurveSource.Gate) :
    (curveDirective bridge mask input source inputKey gate).target =
      if (curveDirective bridge mask input source inputKey gate).bit then
        CurveSource.slope source gate + CurveSource.field source gate
      else CurveSource.field source gate := by
  rcases gate with ⟨adaptor, bit⟩
  fin_cases adaptor <;> rfl

private theorem curveDirective_lift (bridge mask : BaseField) (input : AffineInput)
    (source : CurveMaskSample) (inputKey : InputMacKey) (gate : CurveSource.Gate) :
    (curveDirective bridge mask input source inputKey gate).lift.1 =
      (goodHashLift (curveDirective bridge mask input source inputKey gate).target
        (source.2.2 gate.1 gate.2)).1 := by
  rcases gate with ⟨adaptor, bit⟩
  fin_cases adaptor <;> rfl

theorem curve_actualDirective_record_eq_prescription
    (bridge mask : BaseField) (input : AffineInput) (source : CurveMaskSample)
    (inputKey : InputMacKey) (gate : CurveSource.Gate) (slot : Pipeline.FixedKeySlot) :
    rawSlotBranch slot = (curveDirective bridge mask input source inputKey gate).bit →
      (curveDirective bridge mask input source inputKey gate).slotRecord slot =
        (CurveSource.prescription source inputKey (curveLifts source) gate).slotRecord slot := by
  intro active
  apply GateDirective.slotRecord_eq_raw _ _ slot active
  · exact curveDirective_location bridge mask input source inputKey gate
  · exact curveDirective_window bridge mask input source inputKey gate
  · exact curveDirective_label bridge mask input source inputKey gate
  · exact curveDirective_table bridge mask input source inputKey gate
  · intro branch
    have target := curveDirective_target bridge mask input source inputKey gate
    simp only [branch, Bool.false_eq_true, if_false] at target
    have lifted := curveDirective_lift bridge mask input source inputKey gate
    have selected := lifted.trans (congrArg (fun value : BaseField =>
      (goodHashLift value (source.2.2 gate.1 gate.2)).1) target)
    change liftHashBlocks _ = fullHashLiftBlockEquiv
      (goodHashLiftSource (CurveSource.field source gate, source.2.2 gate.1 gate.2))
    rw [goodHashLiftSource_blocks]
    exact congrArg liftHashBlocks selected
  · intro branch
    have target := curveDirective_target bridge mask input source inputKey gate
    simp only [branch, if_true] at target
    change (curveDirective bridge mask input source inputKey gate).target =
      CurveSource.slope source gate +
        ((goodHashLiftSource (CurveSource.field source gate, source.2.2 gate.1 gate.2)).val : BaseField)
    rw [goodHashLiftSource_field]
    exact target

end Kriterion.ConditionalDisclosure
