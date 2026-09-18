import Proof.Privacy.Simulator.Arithmetic.FixedContinuation
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineComponents
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineFinish

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine
attribute [local irreducible] gateLoopSamples GateLoopReady onlineMachineCode

/-- The point source returns original labels or the public-sampler cutoff state. -/
noncomputable def onlinePointGateResult (result : Bool × Memory × Nat) : Configuration 317804845 × Nat :=
  if result.1 then (⟨317804843, onlineFinalMemory result.2.1⟩, result.2.2 + 200663)
  else (⟨317804844, result.2.1⟩, result.2.2 + 1)

/-- The actual point gate loop closes its exact source and final original-label output. -/
theorem onlineMachine_pointGateRun [BN254.FieldCertificate] (attempts limit : Nat) (memory : Memory)
    (attemptFits : attempts < 2 ^ 256)
    (ready : GateLoopReady pointGatePlan attempts limit 303784 0 memory) :
    ClosedRun (onlineMachine attempts) 2883957 memory
      (gateDriverRunBudget attempts limit * 303784 + 200663)
      ((gateLoopSamples pointGatePlan attempts 303784 0 memory).map onlinePointGateResult) := by
  intro fuel
  have continued := gateLoopBlock_continue (onlineMachine attempts) pointGatePlan attempts limit (by decide)
    (fun pc => onlineBranchLabels 2883957 314720224 (by decide) 317604181 pc.val)
    (onlineMachine_pointGates attempts) 303784 0 (200663 + fuel) memory (by decide) attemptFits ready
  change run (onlineMachine attempts) (gateDriverRunBudget attempts limit * 303784 + (200663 + fuel))
    ⟨2883957, memory⟩ = _ at continued
  rw [Nat.add_assoc, continued, PMF.map_comp, ← PMF.bind_pure_comp]
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  have bound := gateLoopSamples_cost pointGatePlan attempts limit 303784 0 memory attemptFits ready result supported
  cases success : result.1 with
  | false =>
      have label : onlineBranchLabels 2883957 314720224 (by decide) 317604181
          (gateLoopReturn (count := 303784) (0 + 303784) (by decide) false).val = 317804844 := rfl
      rw [label]
      have remaining : gateDriverRunBudget attempts limit * 303784 + (200663 + fuel) - result.2.2 =
          1 + (gateDriverRunBudget attempts limit * 303784 + 200662 + fuel - result.2.2) := by omega
      rw [remaining, onlineMachine_cutoff, PMF.pure_map]
      simp only [onlinePointGateResult, success, Bool.false_eq_true, ↓reduceIte, Function.comp_apply,
        Option.map_some, Nat.add_comm]
  | true =>
      have label : onlineBranchLabels 2883957 314720224 (by decide) 317604181
          (gateLoopReturn (count := 303784) (0 + 303784) (by decide) true).val = 317604181 := rfl
      rw [label]
      have remaining : gateDriverRunBudget attempts limit * 303784 + (200663 + fuel) - result.2.2 =
          200663 + (gateDriverRunBudget attempts limit * 303784 + fuel - result.2.2) := by omega
      rw [remaining, onlineMachine_finish, PMF.pure_map]
      simp only [onlinePointGateResult, success, ↓reduceIte, Function.comp_apply, Option.map_some, Nat.add_comm]

end Kriterion.ArgoMAC.ArithmeticSimulator
