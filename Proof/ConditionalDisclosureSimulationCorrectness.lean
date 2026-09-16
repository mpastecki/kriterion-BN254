import Proof.ConditionalDisclosureSimulator

namespace Kriterion.ConditionalDisclosure.Simulation

open BN254 Cryptography ArgoMAC ArgoMAC.Security
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Collision-free simulator programming evaluates to the supplied real function output.
This consistency theorem is not a bound on the probability of a collision. -/
theorem evaluate_finish [FieldCertificate] [GroupCertificate]
    (state : State) (scalar : ScalarField) (input : AffineInput)
    (invariant : SimulatorInvariant state.oracle)
    (notBad : (state.finish input (checkedScalarMultiplication scalar input)).oracle.bad = false) :
    evaluate (state.finish input (checkedScalarMultiplication scalar input)).view state.table input
      (state.labels input).inputMac = checkedScalarMultiplication scalar input := by
  cases decoded : decodePoint input with
  | none =>
    simp only [evaluate, decoded, checkedScalarMultiplication, Option.map_none]
  | some point =>
    have onCurve : OnCurve input := (decodePoint_defined input).mp (by simp [decoded])
    let initial := state.hashState input (checkedScalarMultiplication scalar input)
    let schedule := (state.selectedCurve input).schedule input (state.labels input).inputMac
    have finalNotBad : (programGateSchedule initial schedule).bad = false := by
      simpa only [State.finish] using notBad
    have initialNotBad : initial.bad = false := by
      cases bad : initial.bad with
      | false => rfl
      | true =>
        have impossible := programGateSchedule_bad_of_bad initial schedule bad
        rw [finalNotBad] at impossible
        cases impossible
    have initialInvariant : SimulatorInvariant initial := by
      dsimp only [initial, State.hashState]
      rw [if_pos onCurve]
      exact tryProgramHash_preservesInvariant _ _ _ invariant
    have satisfied := programGateSchedule_satisfies_of_notBad initial schedule
      initialInvariant finalNotBad
    have curveValue := (state.selectedCurve input).evaluate
      (programGateSchedule initial schedule) input (state.labels input).inputMac satisfied
    simp only [State.selectedCurve, CurveGateRequest.retarget_table,
      CurveGateRequest.retarget_result] at curveValue
    have fresh : freshHashInputCheck state.oracle.hashTranscript state.target = true := by
      by_contra notFresh
      have impossible : initial.bad = true := by
        simp [initial, State.hashState, onCurve, tryProgramHash, notFresh, markBad]
      rw [initialNotBad] at impossible
      cases impossible
    have finalHash : (state.finish input (checkedScalarMultiplication scalar input)).oracle.hashOracle =
        Function.update state.oracle.hashOracle state.target (programValue scalar state.ciphertext) := by
      dsimp only [State.finish]
      rw [programGateSchedule_hashOracle]
      simp only [State.hashState, if_pos onCurve, ScalarRecovery.recover_correct scalar input onCurve,
        tryProgramHash, if_pos fresh, programHash]
    have evaluated :
        evaluate (state.finish input (checkedScalarMultiplication scalar input)).view state.table input
          (state.labels input).inputMac = some (scalarMultiplication scalar point) := by
      unfold evaluate
      rw [decoded]
      dsimp only [State.view, State.table]
      have curveFinal : CurveMembership.evaluate
          (Pipeline.curveOracles (state.finish input (checkedScalarMultiplication scalar input)).oracle.fixedOracle)
          state.curve.table input (state.labels input).inputMac = state.target := by
        simpa only [State.finish] using curveValue
      rw [curveFinal, finalHash, decrypt_program]
    exact evaluated.trans (by simp only [checkedScalarMultiplication, decoded, Option.map_some])

end
end Kriterion.ConditionalDisclosure.Simulation
