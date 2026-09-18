import Proof.Privacy.Simulator.Arithmetic.OnlineTargetLayout
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineLinear
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineComponents
import Proof.Privacy.Simulator.Arithmetic.FixedContinuation

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The private preparation computes all selected targets before the point retarget pass. -/
noncomputable def onlineTargetMemory [BN254.FieldCertificate] [BN254.GroupCertificate]
    (memory : Memory) (output : BN254.Point)
    (sample : (Fin 91 → BN254.Point) × (Fin 92 → BN254.NonZeroBase)) : Memory :=
  outputTargetsMemory (executeLinear onlineTargetSetup memory) output sample

/-- The link entry follows the complete selected-target and point-retarget computation. -/
noncomputable def onlinePreparedMemory [BN254.FieldCertificate] [BN254.GroupCertificate]
    (memory : Memory) (output : BN254.Point)
    (sample : (Fin 91 → BN254.Point) × (Fin 92 → BN254.NonZeroBase)) : Memory :=
  executeLinear onlineLinkSetup (executeLinear retargetPointCode
    (executeLinear onlineRetargetSetup (onlineTargetMemory memory output sample)))

/-- The preparation cost charges every target instruction and all fixed retarget instructions. -/
def onlinePrepareCost [BN254.FieldCertificate] [BN254.GroupCertificate]
    (sample : (Fin 91 → BN254.Point) × (Fin 92 → BN254.NonZeroBase)) : Nat :=
  4 + (outputTargetsCost sample.1 + (3 + (1533922 + 8)))

/-- The actual private preparation returns its exact memory to the public link phase. -/
theorem onlineMachine_prepare [BN254.FieldCertificate] [BN254.GroupCertificate]
    (attempts : Nat) (memory : Memory) (output : BN254.Point)
    (sample : (Fin 91 → BN254.Point) × (Fin 92 → BN254.NonZeroBase))
    (stored : WordsAt memory.ram (BitVec.ofNat 256 onlineSampleBase) 0 (onlineWords sample))
    (selected : selectedOutputPoint memory.ram (BitVec.ofNat 256 onlineInputBase) = some output) :
    FixedContinuation (onlineMachine attempts) 22490 1560762 memory
      (onlinePreparedMemory memory output sample) (onlinePrepareCost sample) := by
  let targetInitial := executeLinear onlineTargetSetup memory
  let retargetInitial := executeLinear onlineRetargetSetup (onlineTargetMemory memory output sample)
  let retargeted := executeLinear retargetPointCode retargetInitial
  have setup := onlineTargetSetup_state memory
  have first : FixedContinuation (onlineMachine attempts) 22490 22494 memory targetInitial 4 := by
    intro fuel
    exact linear_continue (onlineMachine attempts) onlineTargetSetup
      (onlineBodyLabels 22490 4 (by decide) 22494) (onlineMachine_targetSetup attempts) memory fuel
  have targets : FixedContinuation (onlineMachine attempts) 22494 26829 targetInitial
      (onlineTargetMemory memory output sample) (outputTargetsCost sample.1) := by
    intro fuel
    have words : WordsAt targetInitial.ram (targetInitial.registers 14) 0 (onlineWords sample) := by
      rw [show targetInitial.ram = memory.ram from setup.1,
        show targetInitial.registers 14 = BitVec.ofNat 256 onlineSampleBase from setup.2.2.2.2.1]
      exact stored
    have outputWord : selectedOutputPoint targetInitial.ram (targetInitial.registers 11) = some output := by
      rw [show targetInitial.ram = memory.ram from setup.1,
        show targetInitial.registers 11 = BitVec.ofNat 256 onlineInputBase from setup.2.2.2.1]
      exact selected
    have law := outputTargetsBlock_run (onlineMachine attempts)
      (fun pc => onlineBodyLabels 22494 4335 (by decide) 26829 pc.val) (onlineMachine_targets attempts)
      fuel targetInitial output sample (onlineTargetSetup_pointer memory) words outputWord (onlineTargetSetup_separate memory)
    rw [Nat.add_comm fuel (outputTargetsCost sample.1)] at law
    exact law
  have pointSetup : FixedContinuation (onlineMachine attempts) 26829 26832
      (onlineTargetMemory memory output sample) retargetInitial 3 := by
    intro fuel
    exact linear_continue (onlineMachine attempts) onlineRetargetSetup
      (onlineBodyLabels 26829 3 (by decide) 26832) (onlineMachine_retargetSetup attempts)
      (onlineTargetMemory memory output sample) fuel
  have pointRun : FixedContinuation (onlineMachine attempts) 26832 1560754 retargetInitial retargeted 1533922 := by
    intro fuel
    exact retargetPointHost_continue (onlineMachine attempts)
      (onlineBodyLabels 26832 1533922 (by decide) 1560754) (onlineMachine_pointRetarget attempts) retargetInitial fuel
  have linkSetup : FixedContinuation (onlineMachine attempts) 1560754 1560762 retargeted
      (onlinePreparedMemory memory output sample) 8 := by
    intro fuel
    exact linear_continue (onlineMachine attempts) onlineLinkSetup
      (onlineBodyLabels 1560754 8 (by decide) 1560762) (onlineMachine_linkSetup attempts) retargeted fuel
  exact first.trans _ _ _ _ _ _ _ _ _
    (targets.trans _ _ _ _ _ _ _ _ _ (pointSetup.trans _ _ _ _ _ _ _ _ _
      (pointRun.trans _ _ _ _ _ _ _ _ _ linkSetup)))

/-- The complete private preparation has a fixed instruction allowance. -/
theorem onlinePrepareCost_bound [BN254.FieldCertificate] [BN254.GroupCertificate]
    (sample : (Fin 91 → BN254.Point) × (Fin 92 → BN254.NonZeroBase)) :
    onlinePrepareCost sample ≤ 1678841 := by
  have bound := outputTargetsCost_bound sample.1
  unfold onlinePrepareCost
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
