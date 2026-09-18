import Proof.Privacy.Simulator.Arithmetic.OnlineMachinePointGates
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineBranch

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine
attribute [local irreducible] gateLoopSamples GateLoopReady

/-- The present-output branch installs the transformed-label buffer. -/
def onlinePointGateInitial (memory : Memory) : Memory :=
  executeLinear onlinePointSetup (onlineTagMemory memory)

/-- The point branch source includes both setup blocks and the complete point gate loop. -/
noncomputable def onlinePointBranchSamples [BN254.FieldCertificate] (attempts : Nat) (memory : Memory) :
    PMF (Configuration 317804845 × Nat) :=
  ((gateLoopSamples pointGatePlan attempts 303784 0 (onlinePointGateInitial memory)).map onlinePointGateResult).map
    fun result => (result.1, result.2 + 6)

/-- The actual present-output branch runs the point source to its exact halt. -/
theorem onlineMachine_pointBranch [BN254.FieldCertificate] (attempts limit : Nat) (memory : Memory)
    (attemptFits : attempts < 2 ^ 256)
    (present : memory.ram (BitVec.ofNat 256 (onlineInputBase + 2)) ≠ 0)
    (ready : GateLoopReady pointGatePlan attempts limit 303784 0 (onlinePointGateInitial memory)) :
    ClosedRun (onlineMachine attempts) 2883951 memory
      (6 + (gateDriverRunBudget attempts limit * 303784 + 200663))
      (onlinePointBranchSamples attempts memory) := by
  have branch : FixedContinuation (onlineMachine attempts) 2883951 2883954 memory (onlineTagMemory memory) 3 := by
    intro reserve
    have law := onlineMachine_secondBranch_continue attempts reserve memory
    simp only [onlineBranchReturn, if_neg present] at law
    exact law
  have setup : FixedContinuation (onlineMachine attempts) 2883954 2883957
      (onlineTagMemory memory) (onlinePointGateInitial memory) 3 := by
    intro reserve
    exact linear_continue (onlineMachine attempts) onlinePointSetup
      (onlineBodyLabels 2883954 3 (by decide) 2883957) (onlineMachine_pointSetup attempts)
      (onlineTagMemory memory) reserve
  exact (branch.trans _ _ _ _ _ _ _ _ _ setup).close _ _ _ _ _ _ _ _
    (onlineMachine_pointGateRun attempts limit (onlinePointGateInitial memory) attemptFits ready)

end Kriterion.ArgoMAC.ArithmeticSimulator
