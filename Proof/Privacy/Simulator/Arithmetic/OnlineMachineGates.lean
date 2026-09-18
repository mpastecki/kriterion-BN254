import Proof.Privacy.Simulator.Arithmetic.OnlineMachineCurveGates

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The gate phase starts with the original-label buffer for the curve requests. -/
def onlineGateInitial (memory : Memory) : Memory := executeLinear onlineOriginalSetup memory

/-- The complete valid gate source charges its initial buffer setup. -/
noncomputable def onlineGateSamples [BN254.FieldCertificate] (attempts : Nat) (memory : Memory) :
    PMF (Configuration 317804845 × Nat) :=
  (onlineCurvePointSamples attempts (onlineGateInitial memory)).map fun result => (result.1, result.2 + 3)

/-- The complete gate reserve includes both gate phases and the final output. -/
def onlineGateReserve (attempts limit : Nat) : Nat :=
  3 + (gateDriverRunBudget attempts limit * 1270 +
    (6 + (gateDriverRunBudget attempts limit * 303784 + 200663)))

/-- The valid gate readiness contract covers every reached point phase. -/
def OnlineGateReady [BN254.FieldCertificate] (attempts limit : Nat) (memory : Memory) : Prop :=
  GateLoopReady curveGatePlan attempts limit 1270 0 (onlineGateInitial memory) ∧
  ∀ result ∈ (gateLoopSamples curveGatePlan attempts 1270 0 (onlineGateInitial memory)).support,
    result.1 = true → result.2.1.ram (BitVec.ofNat 256 (onlineInputBase + 2)) ≠ 0 ∧
      GateLoopReady pointGatePlan attempts limit 303784 0 (onlinePointGateInitial result.2.1)

/-- The actual valid gate body has the complete source law and exact reserve. -/
theorem onlineMachine_gates [BN254.FieldCertificate] (attempts limit : Nat) (memory : Memory)
    (attemptFits : attempts < 2 ^ 256) (ready : OnlineGateReady attempts limit memory) :
    ClosedRun (onlineMachine attempts) 1568228 memory (onlineGateReserve attempts limit)
      (onlineGateSamples attempts memory) := by
  have setup : FixedContinuation (onlineMachine attempts) 1568228 1568231 memory (onlineGateInitial memory) 3 := by
    intro fuel
    exact linear_continue (onlineMachine attempts) onlineOriginalSetup
      (onlineBodyLabels 1568228 3 (by decide) 1568231) (onlineMachine_curveSetup attempts) memory fuel
  exact setup.close _ _ _ _ _ _ _ _
    (onlineMachine_curvePointRun attempts limit (onlineGateInitial memory) attemptFits ready.1 ready.2)

/-- The valid gate reserve counts all 305054 gates exactly once. -/
theorem onlineGateReserve_eq (attempts limit : Nat) :
    onlineGateReserve attempts limit = gateDriverRunBudget attempts limit * 305054 + 200672 := by
  unfold onlineGateReserve
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
