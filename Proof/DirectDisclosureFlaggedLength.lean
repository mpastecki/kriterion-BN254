import Proof.DirectDisclosureFlaggedMass

namespace Kriterion.DirectDisclosure.FlaggedMass

open Cryptography ArgoMAC.Security
noncomputable section

/-- The internal flag and all private sampling preserve the exact public query budget. -/
theorem length_le {oracle : OracleSpec.{0, 0}}
    {Source State Public First Labels Second : Type}
    (handler : OracleHandler oracle State) {firstBudget secondBudget : Nat}
    (samples : PMF Source) (table : Source → Public) (state : Source → State)
    (choose : Public → OracleProgram oracle First firstBudget)
    (encode : Source → State → First → (Labels × Bool) × State)
    (decide : Public → First → Labels → OracleProgram oracle Second secondBudget)
    (output : (Public × First × List (Sigma oracle.Answer) × Labels × Second ×
      List (Sigma oracle.Answer)) × Bool)
    (member : output ∈ (flaggedTranscript handler samples table state choose encode decide).support) :
    output.1.2.2.1.length + output.1.2.2.2.2.2.length ≤ firstBudget + secondBudget := by
  rw [flaggedTranscript, PMF.mem_support_map_iff] at member
  obtain ⟨raw, member, rfl⟩ := member
  simp only [sampledTwoPhaseTranscript, twoPhaseTranscript,
    PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at member
  obtain ⟨source, _, middle, ⟨first, firstMember, result,
    ⟨encoded, _, last, lastMember, rfl⟩, rfl⟩, rfl⟩ := member
  exact Nat.add_le_add (runOracleProgramWithTranscript_length_le _ _ _ first firstMember)
    (runOracleProgramWithTranscript_length_le _ _ _ last lastMember)

/-- The combined logged transcript obeys the same public budget. -/
theorem append_length_le {oracle : OracleSpec.{0, 0}}
    {Source State Public First Labels Second : Type}
    (handler : OracleHandler oracle State) {firstBudget secondBudget : Nat}
    (samples : PMF Source) (table : Source → Public) (state : Source → State)
    (choose : Public → OracleProgram oracle First firstBudget)
    (encode : Source → State → First → (Labels × Bool) × State)
    (decide : Public → First → Labels → OracleProgram oracle Second secondBudget)
    (output : (Public × First × List (Sigma oracle.Answer) × Labels × Second ×
      List (Sigma oracle.Answer)) × Bool)
    (member : output ∈ (flaggedTranscript handler samples table state choose encode decide).support) :
    (output.1.2.2.1 ++ output.1.2.2.2.2.2).length ≤ firstBudget + secondBudget := by
  rw [List.length_append]
  exact length_le handler samples table state choose encode decide output member

/-- An over-budget flagged transcript has exactly zero point mass. -/
theorem point_mass_eq_zero_of_length_gt {oracle : OracleSpec.{0, 0}}
    {Source State Public First Labels Second : Type}
    (handler : OracleHandler oracle State) {firstBudget secondBudget : Nat}
    (samples : PMF Source) (table : Source → Public) (state : Source → State)
    (choose : Public → OracleProgram oracle First firstBudget)
    (encode : Source → State → First → (Labels × Bool) × State)
    (decide : Public → First → Labels → OracleProgram oracle Second secondBudget)
    (output : (Public × First × List (Sigma oracle.Answer) × Labels × Second ×
      List (Sigma oracle.Answer)) × Bool)
    (tooLong : firstBudget + secondBudget < output.1.2.2.1.length + output.1.2.2.2.2.2.length) :
    flaggedTranscript handler samples table state choose encode decide output = 0 := by
  by_contra nonzero
  exact (Nat.not_le_of_lt tooLong) (length_le handler samples table state choose encode decide output nonzero)

end
end Kriterion.DirectDisclosure.FlaggedMass
