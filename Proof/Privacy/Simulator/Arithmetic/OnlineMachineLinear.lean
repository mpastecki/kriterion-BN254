import Proof.Privacy.Simulator.Arithmetic.OnlineMachineLabels

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine
attribute [local irreducible] onlineMachineCode onlineCurveCode onlinePointCode

/-- The online machine contains its inputSetup instruction block. -/
theorem onlineMachine_inputSetup (attempts : Nat) :
    ContainsLinear (onlineMachine attempts) onlineInputSetup
      (onlineBodyLabels 0 1 (by decide) 1) := by
  intro index inside
  have bound : index < 1 := by exact inside
  change (onlineMachineCode attempts)[ (onlineBodyLabels 0 1 (by decide) 1 index).val ]'(onlineBodyLabels 0 1 (by decide) 1 index).isLt =
    (onlineInputSetup[index]'inside).emit (onlineBodyLabels 0 1 (by decide) 1 (index + 1))
  have next := onlineBodyLabels_next 0 1 (by decide) index bound
  change onlineBodyLabels 0 1 (by decide) 1 (index + 1) = _ at next
  rw [onlineMachineCode_get, next]
  change onlineInstruction attempts ⟨_, _⟩ = _
  have active := onlineBodyLabels_active 0 1 (by decide) 1 index bound
  simp only [active]
  unfold onlineInstruction
  have guard0 : (0 + index < 1) := by omega
  rw [dif_pos guard0]
  simp only [Nat.zero_add]

/-- The online machine contains its originalSetup instruction block. -/
theorem onlineMachine_originalSetup (attempts : Nat) :
    ContainsLinear (onlineMachine attempts) onlineOriginalSetup
      (onlineBodyLabels 98 3 (by decide) 101) := by
  intro index inside
  have bound : index < 3 := by exact inside
  change (onlineMachineCode attempts)[ (onlineBodyLabels 98 3 (by decide) 101 index).val ]'(onlineBodyLabels 98 3 (by decide) 101 index).isLt =
    (onlineOriginalSetup[index]'inside).emit (onlineBodyLabels 98 3 (by decide) 101 (index + 1))
  have next := onlineBodyLabels_next 98 3 (by decide) index bound
  change onlineBodyLabels 98 3 (by decide) 101 (index + 1) = _ at next
  rw [onlineMachineCode_get, next]
  change onlineInstruction attempts ⟨_, _⟩ = _
  have active := onlineBodyLabels_active 98 3 (by decide) 101 index bound
  simp only [active]
  unfold onlineInstruction
  have guard0 : ¬ (98 + index < 1) := by omega
  have guard1 : ¬ (98 + index < 98) := by omega
  have guard2 : (98 + index < 101) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_pos guard2]
  simp only [Nat.add_sub_cancel_left]

/-- The online machine contains its originalStore instruction block. -/
theorem onlineMachine_originalStore (attempts : Nat) :
    ContainsLinear (onlineMachine attempts) selectedLabelStoreCode
      (onlineBodyLabels 101 7112 (by decide) 7213) := by
  intro index inside
  have bound : index < 7112 := by simpa only [selectedLabelStoreCode_length] using inside
  change (onlineMachineCode attempts)[ (onlineBodyLabels 101 7112 (by decide) 7213 index).val ]'(onlineBodyLabels 101 7112 (by decide) 7213 index).isLt =
    (selectedLabelStoreCode[index]'inside).emit (onlineBodyLabels 101 7112 (by decide) 7213 (index + 1))
  have next := onlineBodyLabels_next 101 7112 (by decide) index bound
  change onlineBodyLabels 101 7112 (by decide) 7213 (index + 1) = _ at next
  rw [onlineMachineCode_get, next]
  change onlineInstruction attempts ⟨_, _⟩ = _
  have active := onlineBodyLabels_active 101 7112 (by decide) 7213 index bound
  simp only [active]
  unfold onlineInstruction
  have guard0 : ¬ (101 + index < 1) := by omega
  have guard1 : ¬ (101 + index < 98) := by omega
  have guard2 : ¬ (101 + index < 101) := by omega
  have guard3 : (101 + index < 7213) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_neg guard2, dif_pos guard3]
  simp only [Nat.add_sub_cancel_left]

/-- The online machine contains its curveRetarget instruction block. -/
theorem onlineMachine_curveRetarget (attempts : Nat) :
    ContainsLinear (onlineMachine attempts) retargetCurveCode
      (onlineBodyLabels 7213 6405 (by decide) 13618) := by
  intro index inside
  have bound : index < 6405 := by simpa only [retargetCurveCode_length] using inside
  change (onlineMachineCode attempts)[ (onlineBodyLabels 7213 6405 (by decide) 13618 index).val ]'(onlineBodyLabels 7213 6405 (by decide) 13618 index).isLt =
    (retargetCurveCode[index]'inside).emit (onlineBodyLabels 7213 6405 (by decide) 13618 (index + 1))
  have next := onlineBodyLabels_next 7213 6405 (by decide) index bound
  change onlineBodyLabels 7213 6405 (by decide) 13618 (index + 1) = _ at next
  rw [onlineMachineCode_get, next]
  change onlineInstruction attempts ⟨_, _⟩ = _
  have active := onlineBodyLabels_active 7213 6405 (by decide) 13618 index bound
  simp only [active]
  unfold onlineInstruction
  have guard0 : ¬ (7213 + index < 1) := by omega
  have guard1 : ¬ (7213 + index < 98) := by omega
  have guard2 : ¬ (7213 + index < 101) := by omega
  have guard3 : ¬ (7213 + index < 7213) := by omega
  have guard4 : (7213 + index < 13618) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_neg guard2, dif_neg guard3, dif_pos guard4]
  simp only [Nat.add_sub_cancel_left]

/-- The online machine contains its sampleSetup instruction block. -/
theorem onlineMachine_sampleSetup (attempts : Nat) :
    ContainsLinear (onlineMachine attempts) onlineSampleSetup
      (onlineBodyLabels 13621 1 (by decide) 13622) := by
  intro index inside
  have bound : index < 1 := by exact inside
  change (onlineMachineCode attempts)[ (onlineBodyLabels 13621 1 (by decide) 13622 index).val ]'(onlineBodyLabels 13621 1 (by decide) 13622 index).isLt =
    (onlineSampleSetup[index]'inside).emit (onlineBodyLabels 13621 1 (by decide) 13622 (index + 1))
  have next := onlineBodyLabels_next 13621 1 (by decide) index bound
  change onlineBodyLabels 13621 1 (by decide) 13622 (index + 1) = _ at next
  rw [onlineMachineCode_get, next]
  change onlineInstruction attempts ⟨_, _⟩ = _
  have active := onlineBodyLabels_active 13621 1 (by decide) 13622 index bound
  simp only [active]
  unfold onlineInstruction
  have guard0 : ¬ (13621 + index < 1) := by omega
  have guard1 : ¬ (13621 + index < 98) := by omega
  have guard2 : ¬ (13621 + index < 101) := by omega
  have guard3 : ¬ (13621 + index < 7213) := by omega
  have guard4 : ¬ (13621 + index < 13618) := by omega
  have guard5 : ¬ (13621 + index < 13621) := by omega
  have guard6 : (13621 + index < 13622) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_neg guard2, dif_neg guard3, dif_neg guard4, dif_neg guard5, dif_pos guard6]
  simp only [Nat.add_sub_cancel_left]

/-- The online machine contains its targetSetup instruction block. -/
theorem onlineMachine_targetSetup (attempts : Nat) :
    ContainsLinear (onlineMachine attempts) onlineTargetSetup
      (onlineBodyLabels 22490 4 (by decide) 22494) := by
  intro index inside
  have bound : index < 4 := by exact inside
  change (onlineMachineCode attempts)[ (onlineBodyLabels 22490 4 (by decide) 22494 index).val ]'(onlineBodyLabels 22490 4 (by decide) 22494 index).isLt =
    (onlineTargetSetup[index]'inside).emit (onlineBodyLabels 22490 4 (by decide) 22494 (index + 1))
  have next := onlineBodyLabels_next 22490 4 (by decide) index bound
  change onlineBodyLabels 22490 4 (by decide) 22494 (index + 1) = _ at next
  rw [onlineMachineCode_get, next]
  change onlineInstruction attempts ⟨_, _⟩ = _
  have active := onlineBodyLabels_active 22490 4 (by decide) 22494 index bound
  simp only [active]
  unfold onlineInstruction
  have guard0 : ¬ (22490 + index < 1) := by omega
  have guard1 : ¬ (22490 + index < 98) := by omega
  have guard2 : ¬ (22490 + index < 101) := by omega
  have guard3 : ¬ (22490 + index < 7213) := by omega
  have guard4 : ¬ (22490 + index < 13618) := by omega
  have guard5 : ¬ (22490 + index < 13621) := by omega
  have guard6 : ¬ (22490 + index < 13622) := by omega
  have guard7 : ¬ (22490 + index < 22490) := by omega
  have guard8 : (22490 + index < 22494) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_neg guard2, dif_neg guard3, dif_neg guard4, dif_neg guard5, dif_neg guard6, dif_neg guard7, dif_pos guard8]
  simp only [Nat.add_sub_cancel_left]

/-- The online machine contains its retargetSetup instruction block. -/
theorem onlineMachine_retargetSetup (attempts : Nat) :
    ContainsLinear (onlineMachine attempts) onlineRetargetSetup
      (onlineBodyLabels 26829 3 (by decide) 26832) := by
  intro index inside
  have bound : index < 3 := by exact inside
  change (onlineMachineCode attempts)[ (onlineBodyLabels 26829 3 (by decide) 26832 index).val ]'(onlineBodyLabels 26829 3 (by decide) 26832 index).isLt =
    (onlineRetargetSetup[index]'inside).emit (onlineBodyLabels 26829 3 (by decide) 26832 (index + 1))
  have next := onlineBodyLabels_next 26829 3 (by decide) index bound
  change onlineBodyLabels 26829 3 (by decide) 26832 (index + 1) = _ at next
  rw [onlineMachineCode_get, next]
  change onlineInstruction attempts ⟨_, _⟩ = _
  have active := onlineBodyLabels_active 26829 3 (by decide) 26832 index bound
  simp only [active]
  unfold onlineInstruction
  have guard0 : ¬ (26829 + index < 1) := by omega
  have guard1 : ¬ (26829 + index < 98) := by omega
  have guard2 : ¬ (26829 + index < 101) := by omega
  have guard3 : ¬ (26829 + index < 7213) := by omega
  have guard4 : ¬ (26829 + index < 13618) := by omega
  have guard5 : ¬ (26829 + index < 13621) := by omega
  have guard6 : ¬ (26829 + index < 13622) := by omega
  have guard7 : ¬ (26829 + index < 22490) := by omega
  have guard8 : ¬ (26829 + index < 22494) := by omega
  have guard9 : ¬ (26829 + index < 26829) := by omega
  have guard10 : (26829 + index < 26832) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_neg guard2, dif_neg guard3, dif_neg guard4, dif_neg guard5, dif_neg guard6, dif_neg guard7, dif_neg guard8, dif_neg guard9, dif_pos guard10]
  simp only [Nat.add_sub_cancel_left]

/-- The online machine contains its pointRetarget instruction block. -/
theorem onlineMachine_pointRetarget (attempts : Nat) :
    ContainsLinear (onlineMachine attempts) retargetPointCode
      (onlineBodyLabels 26832 1533922 (by decide) 1560754) := by
  intro index inside
  have bound : index < 1533922 := by simpa only [retargetPointCode_length] using inside
  change (onlineMachineCode attempts)[ (onlineBodyLabels 26832 1533922 (by decide) 1560754 index).val ]'(onlineBodyLabels 26832 1533922 (by decide) 1560754 index).isLt =
    (retargetPointCode[index]'inside).emit (onlineBodyLabels 26832 1533922 (by decide) 1560754 (index + 1))
  have next := onlineBodyLabels_next 26832 1533922 (by decide) index bound
  change onlineBodyLabels 26832 1533922 (by decide) 1560754 (index + 1) = _ at next
  rw [onlineMachineCode_get, next]
  change onlineInstruction attempts ⟨_, _⟩ = _
  have active := onlineBodyLabels_active 26832 1533922 (by decide) 1560754 index bound
  simp only [active]
  unfold onlineInstruction
  have guard0 : ¬ (26832 + index < 1) := by omega
  have guard1 : ¬ (26832 + index < 98) := by omega
  have guard2 : ¬ (26832 + index < 101) := by omega
  have guard3 : ¬ (26832 + index < 7213) := by omega
  have guard4 : ¬ (26832 + index < 13618) := by omega
  have guard5 : ¬ (26832 + index < 13621) := by omega
  have guard6 : ¬ (26832 + index < 13622) := by omega
  have guard7 : ¬ (26832 + index < 22490) := by omega
  have guard8 : ¬ (26832 + index < 22494) := by omega
  have guard9 : ¬ (26832 + index < 26829) := by omega
  have guard10 : ¬ (26832 + index < 26832) := by omega
  have guard11 : (26832 + index < 1560754) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_neg guard2, dif_neg guard3, dif_neg guard4, dif_neg guard5, dif_neg guard6, dif_neg guard7, dif_neg guard8, dif_neg guard9, dif_neg guard10, dif_pos guard11]
  simp only [Nat.add_sub_cancel_left]

/-- The online machine contains its linkSetup instruction block. -/
theorem onlineMachine_linkSetup (attempts : Nat) :
    ContainsLinear (onlineMachine attempts) onlineLinkSetup
      (onlineBodyLabels 1560754 8 (by decide) 1560762) := by
  intro index inside
  have bound : index < 8 := by exact inside
  change (onlineMachineCode attempts)[ (onlineBodyLabels 1560754 8 (by decide) 1560762 index).val ]'(onlineBodyLabels 1560754 8 (by decide) 1560762 index).isLt =
    (onlineLinkSetup[index]'inside).emit (onlineBodyLabels 1560754 8 (by decide) 1560762 (index + 1))
  have next := onlineBodyLabels_next 1560754 8 (by decide) index bound
  change onlineBodyLabels 1560754 8 (by decide) 1560762 (index + 1) = _ at next
  rw [onlineMachineCode_get, next]
  change onlineInstruction attempts ⟨_, _⟩ = _
  have active := onlineBodyLabels_active 1560754 8 (by decide) 1560762 index bound
  simp only [active]
  unfold onlineInstruction
  have guard0 : ¬ (1560754 + index < 1) := by omega
  have guard1 : ¬ (1560754 + index < 98) := by omega
  have guard2 : ¬ (1560754 + index < 101) := by omega
  have guard3 : ¬ (1560754 + index < 7213) := by omega
  have guard4 : ¬ (1560754 + index < 13618) := by omega
  have guard5 : ¬ (1560754 + index < 13621) := by omega
  have guard6 : ¬ (1560754 + index < 13622) := by omega
  have guard7 : ¬ (1560754 + index < 22490) := by omega
  have guard8 : ¬ (1560754 + index < 22494) := by omega
  have guard9 : ¬ (1560754 + index < 26829) := by omega
  have guard10 : ¬ (1560754 + index < 26832) := by omega
  have guard11 : ¬ (1560754 + index < 1560754) := by omega
  have guard12 : (1560754 + index < 1560762) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_neg guard2, dif_neg guard3, dif_neg guard4, dif_neg guard5, dif_neg guard6, dif_neg guard7, dif_neg guard8, dif_neg guard9, dif_neg guard10, dif_neg guard11, dif_pos guard12]
  simp only [Nat.add_sub_cancel_left]

/-- The online machine contains its curveSetup instruction block. -/
theorem onlineMachine_curveSetup (attempts : Nat) :
    ContainsLinear (onlineMachine attempts) onlineOriginalSetup
      (onlineBodyLabels 1568228 3 (by decide) 1568231) := by
  intro index inside
  have bound : index < 3 := by exact inside
  change (onlineMachineCode attempts)[ (onlineBodyLabels 1568228 3 (by decide) 1568231 index).val ]'(onlineBodyLabels 1568228 3 (by decide) 1568231 index).isLt =
    (onlineOriginalSetup[index]'inside).emit (onlineBodyLabels 1568228 3 (by decide) 1568231 (index + 1))
  have next := onlineBodyLabels_next 1568228 3 (by decide) index bound
  change onlineBodyLabels 1568228 3 (by decide) 1568231 (index + 1) = _ at next
  rw [onlineMachineCode_get, next]
  change onlineInstruction attempts ⟨_, _⟩ = _
  have active := onlineBodyLabels_active 1568228 3 (by decide) 1568231 index bound
  simp only [active]
  unfold onlineInstruction
  have guard0 : ¬ (1568228 + index < 1) := by omega
  have guard1 : ¬ (1568228 + index < 98) := by omega
  have guard2 : ¬ (1568228 + index < 101) := by omega
  have guard3 : ¬ (1568228 + index < 7213) := by omega
  have guard4 : ¬ (1568228 + index < 13618) := by omega
  have guard5 : ¬ (1568228 + index < 13621) := by omega
  have guard6 : ¬ (1568228 + index < 13622) := by omega
  have guard7 : ¬ (1568228 + index < 22490) := by omega
  have guard8 : ¬ (1568228 + index < 22494) := by omega
  have guard9 : ¬ (1568228 + index < 26829) := by omega
  have guard10 : ¬ (1568228 + index < 26832) := by omega
  have guard11 : ¬ (1568228 + index < 1560754) := by omega
  have guard12 : ¬ (1568228 + index < 1560762) := by omega
  have guard13 : ¬ (1568228 + index < 1568228) := by omega
  have guard14 : (1568228 + index < 1568231) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_neg guard2, dif_neg guard3, dif_neg guard4, dif_neg guard5, dif_neg guard6, dif_neg guard7, dif_neg guard8, dif_neg guard9, dif_neg guard10, dif_neg guard11, dif_neg guard12, dif_neg guard13, dif_pos guard14]
  simp only [Nat.add_sub_cancel_left]

/-- The online machine contains its pointSetup instruction block. -/
theorem onlineMachine_pointSetup (attempts : Nat) :
    ContainsLinear (onlineMachine attempts) onlinePointSetup
      (onlineBodyLabels 2883954 3 (by decide) 2883957) := by
  intro index inside
  have bound : index < 3 := by exact inside
  change (onlineMachineCode attempts)[ (onlineBodyLabels 2883954 3 (by decide) 2883957 index).val ]'(onlineBodyLabels 2883954 3 (by decide) 2883957 index).isLt =
    (onlinePointSetup[index]'inside).emit (onlineBodyLabels 2883954 3 (by decide) 2883957 (index + 1))
  have next := onlineBodyLabels_next 2883954 3 (by decide) index bound
  change onlineBodyLabels 2883954 3 (by decide) 2883957 (index + 1) = _ at next
  rw [onlineMachineCode_get, next]
  change onlineInstruction attempts ⟨_, _⟩ = _
  have active := onlineBodyLabels_active 2883954 3 (by decide) 2883957 index bound
  simp only [active]
  unfold onlineInstruction
  have guard0 : ¬ (2883954 + index < 1) := by omega
  have guard1 : ¬ (2883954 + index < 98) := by omega
  have guard2 : ¬ (2883954 + index < 101) := by omega
  have guard3 : ¬ (2883954 + index < 7213) := by omega
  have guard4 : ¬ (2883954 + index < 13618) := by omega
  have guard5 : ¬ (2883954 + index < 13621) := by omega
  have guard6 : ¬ (2883954 + index < 13622) := by omega
  have guard7 : ¬ (2883954 + index < 22490) := by omega
  have guard8 : ¬ (2883954 + index < 22494) := by omega
  have guard9 : ¬ (2883954 + index < 26829) := by omega
  have guard10 : ¬ (2883954 + index < 26832) := by omega
  have guard11 : ¬ (2883954 + index < 1560754) := by omega
  have guard12 : ¬ (2883954 + index < 1560762) := by omega
  have guard13 : ¬ (2883954 + index < 1568228) := by omega
  have guard14 : ¬ (2883954 + index < 1568231) := by omega
  have guard15 : ¬ (2883954 + index < 2883951) := by omega
  have guard16 : ¬ (2883954 + index < 2883954) := by omega
  have guard17 : (2883954 + index < 2883957) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_neg guard2, dif_neg guard3, dif_neg guard4, dif_neg guard5, dif_neg guard6, dif_neg guard7, dif_neg guard8, dif_neg guard9, dif_neg guard10, dif_neg guard11, dif_neg guard12, dif_neg guard13, dif_neg guard14, dif_neg guard15, dif_neg guard16, dif_pos guard17]
  simp only [Nat.add_sub_cancel_left]

/-- The online machine contains its labelSetup instruction block. -/
theorem onlineMachine_labelSetup (attempts : Nat) :
    ContainsLinear (onlineMachine attempts) onlineLabelSetup
      (onlineBodyLabels 317604181 2 (by decide) 317604183) := by
  intro index inside
  have bound : index < 2 := by exact inside
  change (onlineMachineCode attempts)[ (onlineBodyLabels 317604181 2 (by decide) 317604183 index).val ]'(onlineBodyLabels 317604181 2 (by decide) 317604183 index).isLt =
    (onlineLabelSetup[index]'inside).emit (onlineBodyLabels 317604181 2 (by decide) 317604183 (index + 1))
  have next := onlineBodyLabels_next 317604181 2 (by decide) index bound
  change onlineBodyLabels 317604181 2 (by decide) 317604183 (index + 1) = _ at next
  rw [onlineMachineCode_get, next]
  change onlineInstruction attempts ⟨_, _⟩ = _
  have active := onlineBodyLabels_active 317604181 2 (by decide) 317604183 index bound
  simp only [active]
  unfold onlineInstruction
  have guard0 : ¬ (317604181 + index < 1) := by omega
  have guard1 : ¬ (317604181 + index < 98) := by omega
  have guard2 : ¬ (317604181 + index < 101) := by omega
  have guard3 : ¬ (317604181 + index < 7213) := by omega
  have guard4 : ¬ (317604181 + index < 13618) := by omega
  have guard5 : ¬ (317604181 + index < 13621) := by omega
  have guard6 : ¬ (317604181 + index < 13622) := by omega
  have guard7 : ¬ (317604181 + index < 22490) := by omega
  have guard8 : ¬ (317604181 + index < 22494) := by omega
  have guard9 : ¬ (317604181 + index < 26829) := by omega
  have guard10 : ¬ (317604181 + index < 26832) := by omega
  have guard11 : ¬ (317604181 + index < 1560754) := by omega
  have guard12 : ¬ (317604181 + index < 1560762) := by omega
  have guard13 : ¬ (317604181 + index < 1568228) := by omega
  have guard14 : ¬ (317604181 + index < 1568231) := by omega
  have guard15 : ¬ (317604181 + index < 2883951) := by omega
  have guard16 : ¬ (317604181 + index < 2883954) := by omega
  have guard17 : ¬ (317604181 + index < 2883957) := by omega
  have guard18 : ¬ (317604181 + index < 317604181) := by omega
  have guard19 : (317604181 + index < 317604183) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_neg guard2, dif_neg guard3, dif_neg guard4, dif_neg guard5, dif_neg guard6, dif_neg guard7, dif_neg guard8, dif_neg guard9, dif_neg guard10, dif_neg guard11, dif_neg guard12, dif_neg guard13, dif_neg guard14, dif_neg guard15, dif_neg guard16, dif_neg guard17, dif_neg guard18, dif_pos guard19]
  simp only [Nat.add_sub_cancel_left]

/-- The online machine contains its labels instruction block. -/
theorem onlineMachine_labels (attempts : Nat) :
    ContainsLinear (onlineMachine attempts) selectedLabelsCode
      (onlineBodyLabels 317604183 200660 (by decide) 317804843) := by
  intro index inside
  have bound : index < 200660 := by simpa only [selectedLabelsCode_length] using inside
  change (onlineMachineCode attempts)[ (onlineBodyLabels 317604183 200660 (by decide) 317804843 index).val ]'(onlineBodyLabels 317604183 200660 (by decide) 317804843 index).isLt =
    (selectedLabelsCode[index]'inside).emit (onlineBodyLabels 317604183 200660 (by decide) 317804843 (index + 1))
  have next := onlineBodyLabels_next 317604183 200660 (by decide) index bound
  change onlineBodyLabels 317604183 200660 (by decide) 317804843 (index + 1) = _ at next
  rw [onlineMachineCode_get, next]
  change onlineInstruction attempts ⟨_, _⟩ = _
  have active := onlineBodyLabels_active 317604183 200660 (by decide) 317804843 index bound
  simp only [active]
  unfold onlineInstruction
  have guard0 : ¬ (317604183 + index < 1) := by omega
  have guard1 : ¬ (317604183 + index < 98) := by omega
  have guard2 : ¬ (317604183 + index < 101) := by omega
  have guard3 : ¬ (317604183 + index < 7213) := by omega
  have guard4 : ¬ (317604183 + index < 13618) := by omega
  have guard5 : ¬ (317604183 + index < 13621) := by omega
  have guard6 : ¬ (317604183 + index < 13622) := by omega
  have guard7 : ¬ (317604183 + index < 22490) := by omega
  have guard8 : ¬ (317604183 + index < 22494) := by omega
  have guard9 : ¬ (317604183 + index < 26829) := by omega
  have guard10 : ¬ (317604183 + index < 26832) := by omega
  have guard11 : ¬ (317604183 + index < 1560754) := by omega
  have guard12 : ¬ (317604183 + index < 1560762) := by omega
  have guard13 : ¬ (317604183 + index < 1568228) := by omega
  have guard14 : ¬ (317604183 + index < 1568231) := by omega
  have guard15 : ¬ (317604183 + index < 2883951) := by omega
  have guard16 : ¬ (317604183 + index < 2883954) := by omega
  have guard17 : ¬ (317604183 + index < 2883957) := by omega
  have guard18 : ¬ (317604183 + index < 317604181) := by omega
  have guard19 : ¬ (317604183 + index < 317604183) := by omega
  have guard20 : (317604183 + index < 317804843) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_neg guard2, dif_neg guard3, dif_neg guard4, dif_neg guard5, dif_neg guard6, dif_neg guard7, dif_neg guard8, dif_neg guard9, dif_neg guard10, dif_neg guard11, dif_neg guard12, dif_neg guard13, dif_neg guard14, dif_neg guard15, dif_neg guard16, dif_neg guard17, dif_neg guard18, dif_neg guard19, dif_pos guard20]
  simp only [Nat.add_sub_cancel_left]

end Kriterion.ArgoMAC.ArithmeticSimulator
