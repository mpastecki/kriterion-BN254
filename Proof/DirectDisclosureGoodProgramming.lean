import Proof.DirectDisclosureScheduleCollision
import Proof.DirectDisclosureProgramDomains
import Proof.DirectDisclosureSimulationCorrectness

namespace Kriterion.DirectDisclosure.Simulation

open BN254 Cryptography ArgoMAC ArgoMAC.Security
noncomputable section

/-- The actual curve program has no internal pair collision: its physical indices
are pairwise distinct, independently of keys, masks, targets, and table contents. -/
theorem selected_records_pairwise (request : CurveGateRequest) (input : AffineInput) (mac : InputMac) :
    (gateProgramRecords (request.schedule input mac)).Pairwise fun first second =>
      first.index = second.index → first.domain ≠ second.domain ∧ first.range ≠ second.range := by
  have distinct := ConditionalDisclosure.CurveSource.program_indices_nodup request input mac
  change ((gateProgramRecords (request.schedule input mac)).map PermutationRecord.index).Pairwise
    (fun first second => first ≠ second) at distinct
  have pairs := List.pairwise_map.mp distinct
  exact pairs.imp (fun different same => (different same).elim)

/-- The independent-key grid is sufficient for success of the entire actual
selected program; no additional internal collision event is omitted. -/
theorem finish_bad_eq [FieldCertificate] [GroupCertificate]
    (state : State) (input : AffineInput) (output : Option Point)
    (good : ¬ LabelCollision.GridCollision state.oracle.fixedTranscript
      (LabelCollision.selectedUses (state.selectedCurve input output) input) state.inputKey) :
    (state.finish input output).oracle.bad = state.oracle.bad := by
  dsimp only [State.finish, State.hashState]
  exact programGateSchedule_bad_eq_of_pairwise state.oracle _
    (LabelCollision.selected_schedule_fresh (state.selectedCurve input output) input
      state.inputKey state.oracle.fixedTranscript good)
    (selected_records_pairwise (state.selectedCurve input output) input _)

/-- Good prefix programming gives exact evaluation in the actual simulator view. -/
theorem evaluate_finish_of_grid [FieldCertificate] [GroupCertificate]
    (state : State) (scalar : ScalarField) (input : AffineInput)
    (invariant : SimulatorInvariant state.oracle) (clear : state.oracle.bad = false)
    (good : ¬ LabelCollision.GridCollision state.oracle.fixedTranscript
      (LabelCollision.selectedUses
        (state.selectedCurve input (checkedScalarMultiplication scalar input)) input) state.inputKey) :
    evaluate (state.finish input (checkedScalarMultiplication scalar input)).view state.table input
      (state.labels input).inputMac = checkedScalarMultiplication scalar input :=
  evaluate_finish state scalar input invariant
    ((finish_bad_eq state input (checkedScalarMultiplication scalar input) good).trans clear)

end
end Kriterion.DirectDisclosure.Simulation
