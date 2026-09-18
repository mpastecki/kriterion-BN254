import Proof.Privacy.Simulator.Arithmetic.OnlineMachineLabels
import Proof.Privacy.Simulator.Arithmetic.OnlineInputBlock
import Proof.Privacy.Simulator.Arithmetic.OutputTargetsCode
import Proof.Privacy.Simulator.Arithmetic.EncLinkBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine
attribute [local irreducible] onlineMachineCode onlineCurveCode onlinePointCode

/-- The online machine contains its input block. -/
theorem onlineMachine_input (attempts : Nat) :
    ContainsOnlineInput (onlineMachine attempts) (fun label : Fin 98 => onlineBodyLabels 1 97 (by decide) 98 label.val) := by
  intro pc inside
  have bound : pc.val < 97 := inside
  change (onlineMachineCode attempts)[((fun label : Fin 98 => onlineBodyLabels 1 97 (by decide) 98 label.val) pc).val]'((fun label : Fin 98 => onlineBodyLabels 1 97 (by decide) 98 label.val) pc).isLt =
    relocate (fun label : Fin 98 => onlineBodyLabels 1 97 (by decide) 98 label.val) ((onlineInput).code[pc.val])
  simp only [onlineBodyLabels_active _ _ _ _ _ bound]
  rw [onlineMachineCode_get]
  unfold onlineInstruction
  have guard0 : ¬ (1 + pc.val < 1) := by omega
  have guard1 : (1 + pc.val < 98) := by omega
  rw [dif_neg guard0, dif_pos guard1]
  simp only [Nat.add_sub_cancel_left]
  try rw [onlineCurveCode_eq]
  try rw [onlinePointCode_eq]
  rfl

/-- The online machine contains its samples block. -/
theorem onlineMachine_samples (attempts : Nat) :
    ContainsOnlineSampling (onlineMachine attempts) attempts (fun label : Fin 8869 => onlineBodyLabels 13622 8868 (by decide) 22490 label.val) := by
  intro pc inside
  have bound : pc.val < 8868 := inside
  change (onlineMachineCode attempts)[((fun label : Fin 8869 => onlineBodyLabels 13622 8868 (by decide) 22490 label.val) pc).val]'((fun label : Fin 8869 => onlineBodyLabels 13622 8868 (by decide) 22490 label.val) pc).isLt =
    relocate (fun label : Fin 8869 => onlineBodyLabels 13622 8868 (by decide) 22490 label.val) ((onlineSampling attempts).code[pc.val])
  simp only [onlineBodyLabels_active _ _ _ _ _ bound]
  rw [onlineMachineCode_get]
  unfold onlineInstruction
  have guard0 : ¬ (13622 + pc.val < 1) := by omega
  have guard1 : ¬ (13622 + pc.val < 98) := by omega
  have guard2 : ¬ (13622 + pc.val < 101) := by omega
  have guard3 : ¬ (13622 + pc.val < 7213) := by omega
  have guard4 : ¬ (13622 + pc.val < 13618) := by omega
  have guard5 : ¬ (13622 + pc.val < 13621) := by omega
  have guard6 : ¬ (13622 + pc.val < 13622) := by omega
  have guard7 : (13622 + pc.val < 22490) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_neg guard2, dif_neg guard3, dif_neg guard4, dif_neg guard5, dif_neg guard6, dif_pos guard7]
  simp only [Nat.add_sub_cancel_left]
  try rw [onlineCurveCode_eq]
  try rw [onlinePointCode_eq]
  rfl

/-- The online machine contains its targets block. -/
theorem onlineMachine_targets (attempts : Nat) :
    ContainsOutputTargets (onlineMachine attempts) (fun label : Fin 4336 => onlineBodyLabels 22494 4335 (by decide) 26829 label.val) := by
  intro pc inside
  have bound : pc.val < 4335 := inside
  change (onlineMachineCode attempts)[((fun label : Fin 4336 => onlineBodyLabels 22494 4335 (by decide) 26829 label.val) pc).val]'((fun label : Fin 4336 => onlineBodyLabels 22494 4335 (by decide) 26829 label.val) pc).isLt =
    relocate (fun label : Fin 4336 => onlineBodyLabels 22494 4335 (by decide) 26829 label.val) ((outputTargetsMachine).code[pc.val])
  simp only [onlineBodyLabels_active _ _ _ _ _ bound]
  rw [onlineMachineCode_get]
  unfold onlineInstruction
  have guard0 : ¬ (22494 + pc.val < 1) := by omega
  have guard1 : ¬ (22494 + pc.val < 98) := by omega
  have guard2 : ¬ (22494 + pc.val < 101) := by omega
  have guard3 : ¬ (22494 + pc.val < 7213) := by omega
  have guard4 : ¬ (22494 + pc.val < 13618) := by omega
  have guard5 : ¬ (22494 + pc.val < 13621) := by omega
  have guard6 : ¬ (22494 + pc.val < 13622) := by omega
  have guard7 : ¬ (22494 + pc.val < 22490) := by omega
  have guard8 : ¬ (22494 + pc.val < 22494) := by omega
  have guard9 : (22494 + pc.val < 26829) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_neg guard2, dif_neg guard3, dif_neg guard4, dif_neg guard5, dif_neg guard6, dif_neg guard7, dif_neg guard8, dif_pos guard9]
  simp only [Nat.add_sub_cancel_left]
  try rw [onlineCurveCode_eq]
  try rw [onlinePointCode_eq]
  rfl

/-- The online machine contains its link block. -/
theorem onlineMachine_link (attempts : Nat) :
    ContainsEncLink (onlineMachine attempts) attempts (fun label : Fin 7468 => onlineBranchLabels 1560762 7466 (by decide) 1568228 label.val) := by
  intro pc inside
  have bound : pc.val < 7466 := inside
  change (onlineMachineCode attempts)[((fun label : Fin 7468 => onlineBranchLabels 1560762 7466 (by decide) 1568228 label.val) pc).val]'((fun label : Fin 7468 => onlineBranchLabels 1560762 7466 (by decide) 1568228 label.val) pc).isLt =
    relocate (fun label : Fin 7468 => onlineBranchLabels 1560762 7466 (by decide) 1568228 label.val) ((encLink attempts).code[pc.val])
  simp only [onlineBranchLabels_active _ _ _ _ _ bound]
  rw [onlineMachineCode_get]
  unfold onlineInstruction
  have guard0 : ¬ (1560762 + pc.val < 1) := by omega
  have guard1 : ¬ (1560762 + pc.val < 98) := by omega
  have guard2 : ¬ (1560762 + pc.val < 101) := by omega
  have guard3 : ¬ (1560762 + pc.val < 7213) := by omega
  have guard4 : ¬ (1560762 + pc.val < 13618) := by omega
  have guard5 : ¬ (1560762 + pc.val < 13621) := by omega
  have guard6 : ¬ (1560762 + pc.val < 13622) := by omega
  have guard7 : ¬ (1560762 + pc.val < 22490) := by omega
  have guard8 : ¬ (1560762 + pc.val < 22494) := by omega
  have guard9 : ¬ (1560762 + pc.val < 26829) := by omega
  have guard10 : ¬ (1560762 + pc.val < 26832) := by omega
  have guard11 : ¬ (1560762 + pc.val < 1560754) := by omega
  have guard12 : ¬ (1560762 + pc.val < 1560762) := by omega
  have guard13 : (1560762 + pc.val < 1568228) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_neg guard2, dif_neg guard3, dif_neg guard4, dif_neg guard5, dif_neg guard6, dif_neg guard7, dif_neg guard8, dif_neg guard9, dif_neg guard10, dif_neg guard11, dif_neg guard12, dif_pos guard13]
  simp only [Nat.add_sub_cancel_left]
  try rw [onlineCurveCode_eq]
  try rw [onlinePointCode_eq]
  rfl

/-- The online machine contains its curveGates block. -/
theorem onlineMachine_curveGates (attempts : Nat) :
    ContainsGateLoop (onlineMachine attempts) curveGatePlan attempts (by decide) (fun label : Fin 1315722 => onlineBranchLabels 1568231 1315720 (by decide) 2883951 label.val) := by
  intro pc inside
  have bound : pc.val < 1315720 := inside
  change (onlineMachineCode attempts)[((fun label : Fin 1315722 => onlineBranchLabels 1568231 1315720 (by decide) 2883951 label.val) pc).val]'((fun label : Fin 1315722 => onlineBranchLabels 1568231 1315720 (by decide) 2883951 label.val) pc).isLt =
    relocate (fun label : Fin 1315722 => onlineBranchLabels 1568231 1315720 (by decide) 2883951 label.val) ((gateLoop curveGatePlan attempts (by decide)).code[pc.val])
  simp only [onlineBranchLabels_active _ _ _ _ _ bound]
  rw [onlineMachineCode_get]
  unfold onlineInstruction
  have guard0 : ¬ (1568231 + pc.val < 1) := by omega
  have guard1 : ¬ (1568231 + pc.val < 98) := by omega
  have guard2 : ¬ (1568231 + pc.val < 101) := by omega
  have guard3 : ¬ (1568231 + pc.val < 7213) := by omega
  have guard4 : ¬ (1568231 + pc.val < 13618) := by omega
  have guard5 : ¬ (1568231 + pc.val < 13621) := by omega
  have guard6 : ¬ (1568231 + pc.val < 13622) := by omega
  have guard7 : ¬ (1568231 + pc.val < 22490) := by omega
  have guard8 : ¬ (1568231 + pc.val < 22494) := by omega
  have guard9 : ¬ (1568231 + pc.val < 26829) := by omega
  have guard10 : ¬ (1568231 + pc.val < 26832) := by omega
  have guard11 : ¬ (1568231 + pc.val < 1560754) := by omega
  have guard12 : ¬ (1568231 + pc.val < 1560762) := by omega
  have guard13 : ¬ (1568231 + pc.val < 1568228) := by omega
  have guard14 : ¬ (1568231 + pc.val < 1568231) := by omega
  have guard15 : (1568231 + pc.val < 2883951) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_neg guard2, dif_neg guard3, dif_neg guard4, dif_neg guard5, dif_neg guard6, dif_neg guard7, dif_neg guard8, dif_neg guard9, dif_neg guard10, dif_neg guard11, dif_neg guard12, dif_neg guard13, dif_neg guard14, dif_pos guard15]
  simp only [Nat.add_sub_cancel_left]
  try rw [onlineCurveCode_eq]
  try rw [onlinePointCode_eq]
  rfl

/-- The online machine contains its pointGates block. -/
theorem onlineMachine_pointGates (attempts : Nat) :
    ContainsGateLoop (onlineMachine attempts) pointGatePlan attempts (by decide) (fun label : Fin 314720226 => onlineBranchLabels 2883957 314720224 (by decide) 317604181 label.val) := by
  intro pc inside
  have bound : pc.val < 314720224 := inside
  change (onlineMachineCode attempts)[((fun label : Fin 314720226 => onlineBranchLabels 2883957 314720224 (by decide) 317604181 label.val) pc).val]'((fun label : Fin 314720226 => onlineBranchLabels 2883957 314720224 (by decide) 317604181 label.val) pc).isLt =
    relocate (fun label : Fin 314720226 => onlineBranchLabels 2883957 314720224 (by decide) 317604181 label.val) ((gateLoop pointGatePlan attempts (by decide)).code[pc.val])
  simp only [onlineBranchLabels_active _ _ _ _ _ bound]
  rw [onlineMachineCode_get]
  unfold onlineInstruction
  have guard0 : ¬ (2883957 + pc.val < 1) := by omega
  have guard1 : ¬ (2883957 + pc.val < 98) := by omega
  have guard2 : ¬ (2883957 + pc.val < 101) := by omega
  have guard3 : ¬ (2883957 + pc.val < 7213) := by omega
  have guard4 : ¬ (2883957 + pc.val < 13618) := by omega
  have guard5 : ¬ (2883957 + pc.val < 13621) := by omega
  have guard6 : ¬ (2883957 + pc.val < 13622) := by omega
  have guard7 : ¬ (2883957 + pc.val < 22490) := by omega
  have guard8 : ¬ (2883957 + pc.val < 22494) := by omega
  have guard9 : ¬ (2883957 + pc.val < 26829) := by omega
  have guard10 : ¬ (2883957 + pc.val < 26832) := by omega
  have guard11 : ¬ (2883957 + pc.val < 1560754) := by omega
  have guard12 : ¬ (2883957 + pc.val < 1560762) := by omega
  have guard13 : ¬ (2883957 + pc.val < 1568228) := by omega
  have guard14 : ¬ (2883957 + pc.val < 1568231) := by omega
  have guard15 : ¬ (2883957 + pc.val < 2883951) := by omega
  have guard16 : ¬ (2883957 + pc.val < 2883954) := by omega
  have guard17 : ¬ (2883957 + pc.val < 2883957) := by omega
  have guard18 : (2883957 + pc.val < 317604181) := by omega
  rw [dif_neg guard0, dif_neg guard1, dif_neg guard2, dif_neg guard3, dif_neg guard4, dif_neg guard5, dif_neg guard6, dif_neg guard7, dif_neg guard8, dif_neg guard9, dif_neg guard10, dif_neg guard11, dif_neg guard12, dif_neg guard13, dif_neg guard14, dif_neg guard15, dif_neg guard16, dif_neg guard17, dif_pos guard18]
  simp only [Nat.add_sub_cancel_left]
  try rw [onlineCurveCode_eq]
  try rw [onlinePointCode_eq]
  rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
