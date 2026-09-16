import Proof.DirectDisclosureFlaggedMass

namespace Kriterion.DirectDisclosure.FlaggedMass

open Cryptography ArgoMAC.Security
noncomputable section

/-- Every supported flagged transcript has actual compatible reference states for
both logged phases, including all public query kinds and private adversary samples. -/
theorem support_references {oracle : OracleSpec.{0, 0}}
    {Source State Public First Labels Second : Type}
    (handler : OracleHandler oracle State) {firstBudget secondBudget : Nat}
    (samples : PMF Source) (table : Source → Public) (state : Source → State)
    (choose : Public → OracleProgram oracle First firstBudget)
    (encode : Source → State → First → (Labels × Bool) × State)
    (decide : Public → First → Labels → OracleProgram oracle Second secondBudget)
    (output : (Public × First × List (Sigma oracle.Answer) × Labels × Second ×
      List (Sigma oracle.Answer)) × Bool)
    (member : output ∈ (flaggedTranscript handler samples table state choose encode decide).support) :
    ∃ referenceBefore referenceAfter : State,
      OracleTranscriptCompatible handler referenceBefore output.1.2.2.1 ∧
      OracleTranscriptCompatible handler referenceAfter output.1.2.2.2.2.2 := by
  rw [flaggedTranscript, PMF.mem_support_map_iff] at member
  obtain ⟨raw, member, rfl⟩ := member
  simp only [sampledTwoPhaseTranscript, twoPhaseTranscript,
    PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at member
  obtain ⟨source, _, middle, ⟨first, firstMember, result,
    ⟨encoded, _, last, lastMember, rfl⟩, rfl⟩, rfl⟩ := member
  exact ⟨state source, encoded.2,
    runOracleProgramWithTranscript_compatible _ _ _ first firstMember,
    runOracleProgramWithTranscript_compatible _ _ _ last lastMember⟩

/-- Nonzero point mass supplies both reference witnesses without restricting the
public transcript argument in a subsequent pointwise factorization. -/
theorem nonzero_references {oracle : OracleSpec.{0, 0}}
    {Source State Public First Labels Second : Type}
    (handler : OracleHandler oracle State) {firstBudget secondBudget : Nat}
    (samples : PMF Source) (table : Source → Public) (state : Source → State)
    (choose : Public → OracleProgram oracle First firstBudget)
    (encode : Source → State → First → (Labels × Bool) × State)
    (decide : Public → First → Labels → OracleProgram oracle Second secondBudget)
    (output : (Public × First × List (Sigma oracle.Answer) × Labels × Second ×
      List (Sigma oracle.Answer)) × Bool)
    (nonzero : flaggedTranscript handler samples table state choose encode decide output ≠ 0) :
    ∃ referenceBefore referenceAfter : State,
      OracleTranscriptCompatible handler referenceBefore output.1.2.2.1 ∧
      OracleTranscriptCompatible handler referenceAfter output.1.2.2.2.2.2 :=
  support_references handler samples table state choose encode decide output nonzero

end
end Kriterion.DirectDisclosure.FlaggedMass
