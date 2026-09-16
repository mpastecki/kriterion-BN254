import Proof.Privacy.Source.CrossSourceMass

namespace Kriterion.DirectDisclosure.FlaggedMass

open Cryptography ArgoMAC.Security
open scoped ENNReal
noncomputable section

/-- Move the internal encoding flag outside the ordinary transcript without losing a field. -/
def transcriptEquiv {Public First Labels Second History : Type} :
    (Public × First × History × (Labels × Bool) × Second × History) ≃
      (Public × First × History × Labels × Second × History) × Bool where
  toFun value := ((value.1, value.2.1, value.2.2.1, value.2.2.2.1.1,
    value.2.2.2.2.1, value.2.2.2.2.2), value.2.2.2.1.2)
  invFun value := (value.1.1, value.1.2.1, value.1.2.2.1,
    (value.1.2.2.2.1, value.2), value.1.2.2.2.2.1, value.1.2.2.2.2.2)
  left_inv _value := rfl
  right_inv _value := rfl

private theorem map_equiv_apply {A B : Type} (distribution : PMF A) (equiv : A ≃ B) (value : B) :
    (distribution.map equiv) value = distribution (equiv.symm value) := by
  classical
  rw [PMF.map_apply, tsum_eq_single (equiv.symm value)]
  · simp
  · intro other different
    have unequal : value ≠ equiv other := by
      intro equal
      apply different
      exact (equiv.symm_apply_apply other).symm.trans (congrArg equiv.symm equal.symm)
    simp only [if_neg unequal]

/-- The source flag stays internal: the unchanged second-phase program receives only labels. -/
def flaggedTranscript {oracle : OracleSpec.{0, 0}}
    {Source State Public First Labels Second : Type}
    (handler : OracleHandler oracle State) {firstBudget secondBudget : Nat}
    (samples : PMF Source) (table : Source → Public) (state : Source → State)
    (choose : Public → OracleProgram oracle First firstBudget)
    (encode : Source → State → First → (Labels × Bool) × State)
    (decide : Public → First → Labels → OracleProgram oracle Second secondBudget) :
    PMF ((Public × First × List (Sigma oracle.Answer) × Labels × Second ×
      List (Sigma oracle.Answer)) × Bool) :=
  (sampledTwoPhaseTranscript handler samples table state choose
    (fun source prior selected => PMF.pure (encode source prior selected))
    (fun visible selected pair => decide visible selected pair.1)).map transcriptEquiv

/-- Pointwise exact factorization of the flagged transcript with any compatible
reference handler. Both ordinary adversary weights are unchanged by the internal flag. -/
theorem mass_factor {oracle : OracleSpec.{0, 0}}
    {Source State Other Public First Labels Second : Type}
    (handler : OracleHandler oracle State) (other : OracleHandler oracle Other)
    {firstBudget secondBudget : Nat}
    (samples : PMF Source) (table : Source → Public) (state : Source → State)
    (choose : Public → OracleProgram oracle First firstBudget)
    (encode : Source → State → First → (Labels × Bool) × State)
    (decide : Public → First → Labels → OracleProgram oracle Second secondBudget)
    (referenceBefore referenceAfter : Other)
    (publicTable : Public) (selected : First) (labels : Labels) (decision : Second)
    (before after : List (Sigma oracle.Answer)) (flag : Bool)
    (firstCompatible : OracleTranscriptCompatible other referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible other referenceAfter after) :
    flaggedTranscript handler samples table state choose encode decide
      ((publicTable, selected, before, labels, decision, after), flag) =
      ((runOracleProgramWithTranscript other (choose publicTable) referenceBefore).map
        (fun output => (output.1, output.2.2))) (selected, before) *
      ((runOracleProgramWithTranscript other (decide publicTable selected labels) referenceAfter).map
        (fun output => (output.1, output.2.2))) (decision, after) *
      sampledTwoPhaseSourceMass handler samples table state
        (fun source prior chosen => PMF.pure (encode source prior chosen))
        publicTable selected (labels, flag) before after := by
  rw [flaggedTranscript, map_equiv_apply]
  exact sampledTwoPhaseTranscript_mass_factor_cross handler other samples table state choose
    (fun source prior chosen => PMF.pure (encode source prior chosen))
    (fun visible chosen pair => decide visible chosen pair.1)
    referenceBefore referenceAfter publicTable selected (labels, flag) decision before after
    firstCompatible secondCompatible

/-- The unflagged point has precisely the source mass requesting `(labels, false)`. -/
theorem false_mass_factor {oracle : OracleSpec.{0, 0}}
    {Source State Other Public First Labels Second : Type}
    (handler : OracleHandler oracle State) (other : OracleHandler oracle Other)
    {firstBudget secondBudget : Nat}
    (samples : PMF Source) (table : Source → Public) (state : Source → State)
    (choose : Public → OracleProgram oracle First firstBudget)
    (encode : Source → State → First → (Labels × Bool) × State)
    (decide : Public → First → Labels → OracleProgram oracle Second secondBudget)
    (referenceBefore referenceAfter : Other)
    (publicTable : Public) (selected : First) (labels : Labels) (decision : Second)
    (before after : List (Sigma oracle.Answer))
    (firstCompatible : OracleTranscriptCompatible other referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible other referenceAfter after) :
    flaggedTranscript handler samples table state choose encode decide
      ((publicTable, selected, before, labels, decision, after), false) =
      ((runOracleProgramWithTranscript other (choose publicTable) referenceBefore).map
        (fun output => (output.1, output.2.2))) (selected, before) *
      ((runOracleProgramWithTranscript other (decide publicTable selected labels) referenceAfter).map
        (fun output => (output.1, output.2.2))) (decision, after) *
      sampledTwoPhaseSourceMass handler samples table state
        (fun source prior chosen => PMF.pure (encode source prior chosen))
        publicTable selected (labels, false) before after :=
  mass_factor handler other samples table state choose encode decide referenceBefore referenceAfter
    publicTable selected labels decision before after false firstCompatible secondCompatible

end
end Kriterion.DirectDisclosure.FlaggedMass
