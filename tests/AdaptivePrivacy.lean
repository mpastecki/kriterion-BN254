import Submission
import Components
import Correctness
import E2E
import Operational
import Lean

open Kriterion Kriterion.BN254

example : Kriterion.Solution := Submission.solution

theorem paperCTPRFHas100Bits :
    Cryptography.Assumptions.ConcreteBound 100
      ArgoMAC.Security.permutationWork ArgoMAC.Security.paperConcreteCTPRFError :=
  ArgoMAC.Security.paperConcreteCTPRFHas100Bits

theorem bucketedCTPRFHas100Bits :
    Cryptography.Assumptions.ConcreteBound 100
      ArgoMAC.Security.permutationWork ArgoMAC.Security.bucketedCTPRFError :=
  ArgoMAC.Security.bucketedCTPRFHas100Bits

theorem hashLiftRoundingArithmeticHas100Bits :
    Cryptography.Assumptions.WorkPerAdvantage 100 1
      ArgoMAC.Security.hashLiftRoundingError :=
  ArgoMAC.Security.hashLiftRoundingArithmeticHas100Bits

namespace TranscriptRegression

open Cryptography ArgoMAC.Security

universe uQuery uAnswer uResult uState

/-- This reference preserves the public transcript rules from before the VCV-io migration. -/
private noncomputable def reference {oracle : OracleSpec.{uQuery, uAnswer}}
    {Result : Type uResult} {State : Type uState} (handler : OracleHandler oracle State) :
    {budget : Nat} → OracleProgram oracle Result budget → State →
      PMF (Result × State × List (Sigma oracle.Answer))
  | _, .pure result, state => result.map fun value => (value, state, [])
  | _, .query request next, state =>
      let answer := handler request state
      (reference handler (next answer.1) answer.2).map
        fun output => (output.1, output.2.1, ⟨request, answer.1⟩ :: output.2.2)
  | _, .sample distribution next, state =>
      distribution.bind fun value => reference handler (next value) state

/-- VCV-io preserves every public answer and its order for every program. -/
theorem transcript_eq_reference {oracle : OracleSpec.{uQuery, uAnswer}}
    {Result : Type uResult} {State : Type uState} (handler : OracleHandler oracle State)
    {budget : Nat} (program : OracleProgram oracle Result budget) (state : State) :
    runOracleProgramWithTranscript handler program state = reference handler program state := by
  induction program generalizing state with
  | pure distribution => simp [reference]
  | query request next ih => simp [reference, ih]
  | sample distribution next ih => simp [reference, ih]

end TranscriptRegression

-- Every imported construction, proof, and test must use only the standard Lean axioms.
run_cmd do
  let env ← Lean.getEnv
  for (name, _) in env.constants.toList do
    let origin := (env.getModuleIdxFor? name).bind fun index => env.header.moduleNames[index.toNat]?
    if (`Kriterion).isPrefixOf name || (`Submission).isPrefixOf name ||
        origin.any (fun moduleName => #[`Construction, `Proof, `Components, `Correctness, `E2E, `Operational].contains moduleName.getRoot) ||
        origin.isNone then
      let illegal := (← Lean.collectAxioms name).filter fun axiomName =>
        !#[`propext, `Classical.choice, `Quot.sound].contains axiomName
      unless illegal.isEmpty do Lean.throwError m!"The declaration {name} uses disallowed axioms: {illegal}"
