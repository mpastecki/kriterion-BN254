import Proof.DirectDisclosureSimulator

namespace Kriterion.DirectDisclosure.Simulation

open BN254 Cryptography ArgoMAC ArgoMAC.Security
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Only the selected fixed permutations change; the complete hash oracle is preserved. -/
theorem finish_hashOracle [FieldCertificate] [GroupCertificate]
    (state : State) (input : AffineInput) (output : Option Point) :
    (state.finish input output).oracle.hashOracle = state.oracle.hashOracle :=
  programGateSchedule_hashOracle _ _

theorem finish_encOracle [FieldCertificate] [GroupCertificate]
    (state : State) (input : AffineInput) (output : Option Point) :
    (state.finish input output).oracle.encOracle = state.oracle.encOracle :=
  programGateSchedule_encOracle _ _

/-- All scalar/input pairs evaluate correctly after a collision-free selected schedule.
This is a consistency implication, not a bound on programming collisions. -/
theorem evaluate_finish [FieldCertificate] [GroupCertificate]
    (state : State) (scalar : ScalarField) (input : AffineInput)
    (invariant : SimulatorInvariant state.oracle)
    (notBad : (state.finish input (checkedScalarMultiplication scalar input)).oracle.bad = false) :
    evaluate (state.finish input (checkedScalarMultiplication scalar input)).view state.table input
      (state.labels input).inputMac = checkedScalarMultiplication scalar input := by
  cases decoded : decodePoint input with
  | none => simp only [evaluate, decoded, checkedScalarMultiplication, Option.map_none]
  | some point =>
    have onCurve : OnCurve input := (decodePoint_defined input).mp (by simp [decoded])
    let schedule := (state.selectedCurve input (checkedScalarMultiplication scalar input)).schedule
      input (state.labels input).inputMac
    have finalNotBad : (programGateSchedule state.oracle schedule).bad = false := notBad
    have satisfied := programGateSchedule_satisfies_of_notBad state.oracle schedule invariant finalNotBad
    have curveValue := (state.selectedCurve input (checkedScalarMultiplication scalar input)).evaluate
      (programGateSchedule state.oracle schedule) input (state.labels input).inputMac satisfied
    simp only [State.selectedCurve, CurveGateRequest.retarget_table,
      CurveGateRequest.retarget_result, State.selectedTarget, if_pos onCurve,
      ScalarRecovery.recover_correct scalar input onCurve] at curveValue
    have curveFinal : CurveMembership.evaluate
        (Pipeline.curveOracles (state.finish input (checkedScalarMultiplication scalar input)).oracle.fixedOracle)
        state.curve.table input (state.labels input).inputMac = embedScalar scalar := curveValue
    unfold evaluate
    rw [decoded]
    dsimp only [State.view, State.table]
    rw [curveFinal, decode_embed]
    simp only [checkedScalarMultiplication, decoded, Option.map_some]

end
end Kriterion.DirectDisclosure.Simulation
