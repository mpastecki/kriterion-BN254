import Proof.ConditionalDisclosureProgramRatio

namespace Kriterion.ConditionalDisclosure.CurveSource

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable transcriptOracleFintype

/-- Positive programmed postquery mass supplies an actual complete permutation
reference. Impossible transcripts have zero mass, with no compatibility premise. -/
theorem programmed_queryMass_zero_of_no_reference
    (state : SimulatorState) (schedule : List GateDirective)
    (queries : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (fresh : FreshRecordSchedule state.fixedTranscript (gateProgramRecords schedule))
    [Nonempty (TranscriptOracle state.fixedTranscript)]
    (absent : ¬ Nonempty (TranscriptOracle
      (programRecordHistory state.fixedTranscript (gateProgramRecords schedule) ++ queries))) :
    ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map (fun oracle =>
      programGateSchedule {state with fixedOracle := oracle.1} schedule)).toOuterMeasure
        {programmed | PermutationTranscriptMatches programmed.fixedOracle queries} = 0 := by
  rw [PMF.toOuterMeasure_map_apply]
  have empty : {oracle : TranscriptOracle state.fixedTranscript |
      PermutationTranscriptMatches (programGateSchedule {state with fixedOracle := oracle.1} schedule).fixedOracle
        queries} = ∅ := by
    ext oracle
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro matching
    rw [programGateSchedule_state state schedule fresh oracle] at matching
    let final := programTranscriptRecords state.fixedTranscript (gateProgramRecords schedule) fresh oracle
    apply absent
    refine ⟨⟨final.1, ?_⟩⟩
    intro record member
    rcases List.mem_append.mp member with old | added
    · exact final.2 record old
    · exact matching record added
  change (PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).toOuterMeasure
    {oracle | PermutationTranscriptMatches
      (programGateSchedule {state with fixedOracle := oracle.1} schedule).fixedOracle queries} = 0
  rw [empty]
  simp

end
end Kriterion.ConditionalDisclosure.CurveSource
