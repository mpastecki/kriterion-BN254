import Proof.Privacy.Simulator.Arithmetic.OnlineMachineNullFinish
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineComponents

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine
attribute [local irreducible] gateLoopSamples GateLoopReady onlineMachineCode

/-- The absent-output source returns original labels or the public-sampler cutoff state. -/
noncomputable def onlineNullGateResult (result : Bool × Memory × Nat) : Configuration 317804845 × Nat :=
  if result.1 then
    (⟨317804843, onlineFinalMemory (onlineTagMemory result.2.1)⟩, result.2.2 + 200666)
  else (⟨317804844, result.2.1⟩, result.2.2 + 1)

/-- The actual curve gate loop closes the absent-output source and its final output. -/
theorem onlineMachine_nullGates [BN254.FieldCertificate] (attempts limit : Nat) (memory : Memory)
    (attemptFits : attempts < 2 ^ 256)
    (ready : GateLoopReady curveGatePlan attempts limit 1270 0 memory)
    (absent : ∀ result ∈ (gateLoopSamples curveGatePlan attempts 1270 0 memory).support,
      result.1 = true → result.2.1.ram (BitVec.ofNat 256 (onlineInputBase + 2)) = 0) :
    ClosedRun (onlineMachine attempts) 1568231 memory
      (gateDriverRunBudget attempts limit * 1270 + 200666)
      ((gateLoopSamples curveGatePlan attempts 1270 0 memory).map onlineNullGateResult) := by
  intro fuel
  have continued := gateLoopBlock_continue (onlineMachine attempts) curveGatePlan attempts limit (by decide)
    (fun pc => onlineBranchLabels 1568231 1315720 (by decide) 2883951 pc.val)
    (onlineMachine_curveGates attempts) 1270 0 (200666 + fuel) memory (by decide) attemptFits ready
  change run (onlineMachine attempts) (gateDriverRunBudget attempts limit * 1270 + (200666 + fuel))
    ⟨1568231, memory⟩ = _ at continued
  rw [Nat.add_assoc, continued, PMF.map_comp, ← PMF.bind_pure_comp]
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  have bound := gateLoopSamples_cost curveGatePlan attempts limit 1270 0 memory attemptFits ready result supported
  cases success : result.1 with
  | false =>
      have label : onlineBranchLabels 1568231 1315720 (by decide) 2883951
          (gateLoopReturn (count := 1270) (0 + 1270) (by decide) result.1).val = 317804844 := by
        rw [success]
        rfl
      simp only [success] at label
      rw [label]
      have remaining : gateDriverRunBudget attempts limit * 1270 + (200666 + fuel) - result.2.2 =
          1 + (gateDriverRunBudget attempts limit * 1270 + 200665 + fuel - result.2.2) := by omega
      rw [remaining, onlineMachine_cutoff, PMF.pure_map]
      simp only [onlineNullGateResult, success, Bool.false_eq_true, ↓reduceIte, Function.comp_apply,
        Option.map_some, Nat.add_comm]
  | true =>
      have label : onlineBranchLabels 1568231 1315720 (by decide) 2883951
          (gateLoopReturn (count := 1270) (0 + 1270) (by decide) result.1).val = 2883951 := by
        rw [success]
        rfl
      simp only [success] at label
      rw [label]
      have remaining : gateDriverRunBudget attempts limit * 1270 + (200666 + fuel) - result.2.2 =
          200666 + (gateDriverRunBudget attempts limit * 1270 + fuel - result.2.2) := by omega
      rw [remaining, onlineMachine_nullFinish attempts _ result.2.1 (absent result supported success), PMF.pure_map]
      simp only [onlineNullGateResult, success, ↓reduceIte, Function.comp_apply, Option.map_some, Nat.add_comm]

end Kriterion.ArgoMAC.ArithmeticSimulator
