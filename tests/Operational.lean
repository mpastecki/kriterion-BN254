import Proof.Privacy.Simulator.Arithmetic.WordInputBlock
import Proof.Privacy.Simulator.SimulatorCutoff
import Proof.Privacy.Simulator.SimulatorFiniteArithmetic
import Proof.Privacy.Simulator.SimulatorSamplingCost
import Proof.Privacy.Simulator.SimulatorTotalSampling

open Kriterion.ArgoMAC Kriterion.ArgoMAC.Security
open Kriterion.ArgoMAC.Security.SimulatorMachine
open Kriterion.ArgoMAC.Security.OperationalOracle
open Kriterion.ArgoMAC.Security.BoundedIntegerSampling
open Kriterion.Cryptography

private def integerSource (size : Nat) (positive : 0 < size) (seed : Nat) : Fin size × Nat :=
  (⟨0, positive⟩, seed + 1)

private def fixedIndex : Pipeline.FixedKeyIndex := ⟨.curve .y4, ⟨0, by decide⟩, .hash 0⟩

private def emptyState : SparseState :=
  ⟨((fun _ => ProgrammedPermutation.empty _), []), ⟨[], [], [], [], none, false⟩⟩

private def collisionTrace : Program combinedSpec (Block × Block) 4 :=
  .query (.inl (.program (fixedIndex, 0, 1))) fun _ =>
  .query (.inr (.fixedForward fixedIndex 0)) fun first =>
  .query (.inl (.program (fixedIndex, 0, 2))) fun _ =>
  .query (.inr (.fixedForward fixedIndex 0)) fun second => .pure (first, second)

private def traceResult :=
  let result := Cost.executeCost integerSource collisionTrace emptyState 0 0
  (result.1.1.1.toNat, result.1.1.2.toNat, result.1.2.1.metadata.bad,
    result.1.2.1.metadata.fixedTranscript.length, result.1.2.2, result.2.1, result.2.2)

/-- The failed program preserves the first mapping and records the collision. -/
example : traceResult = (1, 1, true, 3, 1, 4, 56) := by decide

private def bitSource (width : Nat) (seed : Nat) : Fin (2 ^ width) × Nat :=
  (⟨(if seed = 0 then 3 else 2) % (2 ^ width), Nat.mod_lt _ (Nat.two_pow_pos width)⟩, seed + 1)

/-- One rejected block exhausts the one-retry sampler. -/
example : ((cutoff 3 1).run bitSource 0).1.1 = none := by decide

/-- A second block supplies the requested value after four fair-bit reads. -/
example : (cutoff 3 2).run bitSource 0 = ((some ⟨2, by decide⟩, 2), 4) := by decide

#print axioms operational_small_error
#print axioms cutoffEnvelope_has100Bits
#print axioms Program.cutoff_failure
#print axioms Program.cutoff_bit_bound
#print axioms Cost.executeCost_budget

private def failingBits (width : Nat) (seed : Nat) : Fin (2 ^ width) × Nat :=
  (⟨if seed = 0 then 0 else 2 ^ width - 1, by
    split <;> have := Nat.two_pow_pos width <;> omega⟩, seed + 1)

private def twoDrawTrace : Program combinedSpec Unit 2 :=
  .query (.inr (.fixedForward fixedIndex 0)) fun _ =>
  .query (.inr (.fixedForward fixedIndex 1)) fun _ => .pure ()

/-- Two sampled blocks incur eight rejection-control operations. -/
example : (SimulatorRejectionCost.runWithCost bitSource (cutoff 3 2) 0).2 = (2, 8) := by decide

/-- The total integer sampler returns a valid zero after its retry limit. -/
example : ((totalInteger 3 (by decide) 1).run bitSource 0).1.1 = 0 := by decide

private def totalTrace :=
  let result := Cost.executeTotalCost failingBits 2 twoDrawTrace emptyState 0 0
  (result.1.2.1.metadata.fixedTranscript.length, result.1.2.2, result.2)

/- The total executor continues after the failed draw and records every query. -/
#eval show IO Unit from do
  unless totalTrace == (2, 3, 2, 31, 385) do
    throw (IO.userError "The total sparse execution check failed.")

#print axioms Cost.executeTotalCost_correct
#print axioms Cost.executeTotalCost_resources
#print axioms Cost.executeTotalCost_bits

#print axioms SparsePermutation.forward_joint
#print axioms SparsePermutation.inverse_joint
#print axioms adaptive_joint_law

namespace InputMachineRegression
open Kriterion.ArgoMAC.ArithmeticSimulator Kriterion.Cryptography.BoundedMachine

private def labels (pc : Fin 15) : Fin 16 := ⟨pc.val, by omega⟩

private def readStore : Machine := ⟨15, Vector.ofFn (fun pc : Fin 16 =>
  if inside : pc.val < 14 then
    relocate labels ((wordInput 3).code[pc.val]'(by change pc.val < 15; omega))
  else if pc.val = 14 then .store 8 0 15 else .halt), by decide⟩

private theorem contains : ContainsWordInput readStore 3 labels := by
  intro pc inside
  simp [readStore, labels, inside]

private def initialMemory : Memory := {
  bits := Function.update (fun _ => []) 0 [true, false, true, false]
  registers := Function.update (fun _ => 0) 8 37 }

/-- The caller stores five at its saved address and retains the unread fourth bit. -/
example [Kriterion.BN254.FieldCertificate] :
    (run readStore 29 ⟨0, initialMemory⟩).map
      (Option.map fun result => (result.1.memory.ram 37,
        result.1.memory.bits 0, result.1.memory.registers 7, result.2)) =
      PMF.pure (some (5, [false], 1, 29)) := by
  have continued := wordInputBlock_continue readStore 3 2 labels contains
    initialMemory [true, false, true] [false] rfl rfl (by decide)
  change (run readStore (7 * 3 + 6 + 2) ⟨labels 0, initialMemory⟩).map _ = _
  rw [continued]
  simp [run, step, readStore, labels, inputFinal, inputFrame, inputFold,
    initialMemory, PMF.pure_map, PMF.map_comp, Function.comp_def]

end InputMachineRegression
