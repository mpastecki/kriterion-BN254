import Proof.Privacy.Simulator.Arithmetic.OnlineMachineLinear
import Proof.Privacy.Simulator.Arithmetic.FixedContinuation

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine
attribute [local irreducible] onlineMachineCode onlineCurveCode onlinePointCode

/-- Both terminal instructions halt the actual online machine. -/
theorem onlineMachine_halts (attempts : Nat) :
    (onlineMachineCode attempts)[317804843] = .halt ∧
      (onlineMachineCode attempts)[317804844] = .halt := by
  simp only [onlineMachineCode_get]
  exact ⟨rfl, rfl⟩

/-- The final memory contains the complete original-label output. -/
noncomputable def onlineFinalMemory (memory : Memory) : Memory :=
  executeLinear selectedLabelsCode (executeLinear onlineLabelSetup memory)

private theorem haltAt [BN254.FieldCertificate] (host : Machine) (pc : Fin (host.size + 1))
    (code : host.code[pc.val] = .halt) (fuel : Nat) (memory : Memory) :
    run host (fuel + 1) ⟨pc, memory⟩ = PMF.pure (some (⟨pc, memory⟩, 1)) := by
  simp [run, step, code]

private theorem finishRun [BN254.FieldCertificate] (host : Machine)
    (entry middle last : Fin (host.size + 1)) (initial prepared final : Memory) (fuel firstCost secondCost : Nat)
    (setup : ∀ reserve, run host (firstCost + reserve) ⟨entry, initial⟩ =
      (run host reserve ⟨middle, prepared⟩).map (Option.map fun result => (result.1, result.2 + firstCost)))
    (labels : ∀ reserve, run host (secondCost + reserve) ⟨middle, prepared⟩ =
      (run host reserve ⟨last, final⟩).map (Option.map fun result => (result.1, result.2 + secondCost)))
    (halted : host.code[last.val] = .halt) :
    run host (firstCost + secondCost + 1 + fuel) ⟨entry, initial⟩ =
      PMF.pure (some (⟨last, final⟩, 1 + secondCost + firstCost)) := by
  rw [show firstCost + secondCost + 1 + fuel = firstCost + (secondCost + (fuel + 1)) by omega, setup, labels,
    haltAt host last halted fuel final, PMF.pure_map, PMF.pure_map]
  rfl

/-- The final fixed label block charges its setup, body, and halt. -/
theorem onlineMachine_finish [BN254.FieldCertificate] (attempts fuel : Nat) (memory : Memory) :
    run (onlineMachine attempts) (200663 + fuel) ⟨317604181, memory⟩ =
      PMF.pure (some (⟨317804843, onlineFinalMemory memory⟩, 200663)) := by
  apply finishRun (onlineMachine attempts) 317604181 317604183 317804843 memory
    (executeLinear onlineLabelSetup memory) (onlineFinalMemory memory) fuel 2 200660
  · intro reserve
    exact linear_continue (onlineMachine attempts) onlineLabelSetup
      (onlineBodyLabels 317604181 2 (by decide) 317604183)
      (onlineMachine_labelSetup attempts) memory reserve
  · intro reserve
    exact selectedLabelsHost_continue (onlineMachine attempts)
      (onlineBodyLabels 317604183 200660 (by decide) 317804843)
      (onlineMachine_labels attempts) (executeLinear onlineLabelSetup memory) reserve
  · exact (onlineMachine_halts attempts).1

/-- A cutoff stops before the final label output and charges one halt instruction. -/
theorem onlineMachine_cutoff [BN254.FieldCertificate] (attempts fuel : Nat) (memory : Memory) :
    run (onlineMachine attempts) (1 + fuel) ⟨317804844, memory⟩ =
      PMF.pure (some (⟨317804844, memory⟩, 1)) := by
  rw [Nat.add_comm 1 fuel]
  exact haltAt (onlineMachine attempts) 317804844 (onlineMachine_halts attempts).2 fuel memory

/-- Any positive cutoff reserve returns the exact cutoff state. -/
theorem onlineMachine_cutoffClosed [BN254.FieldCertificate] (attempts reserve : Nat) (memory : Memory)
    (positive : 0 < reserve) :
    ClosedRun (onlineMachine attempts) 317804844 memory reserve
      (PMF.pure (⟨317804844, memory⟩, 1)) := by
  intro fuel
  have amount : reserve + fuel = 1 + (reserve - 1 + fuel) := by omega
  rw [amount, onlineMachine_cutoff, PMF.pure_map]

end Kriterion.ArgoMAC.ArithmeticSimulator
