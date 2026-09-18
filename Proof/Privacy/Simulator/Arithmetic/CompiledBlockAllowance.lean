import Proof.Privacy.Simulator.Arithmetic.RecordedPublicHandlerRun
import Proof.Privacy.Simulator.Arithmetic.GateSchedule

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- This sum reserves the checked block costs and one control allowance for final assembly. -/
def compiledBlockAllowance (queries : Nat) : Nat :=
  let limit := queries + 915671
  605084290688 + 120738687 +
    305054 * (7722 * 256 + 168 * limit + 1763) +
    305054 * 12812 + 7468 +
    508 * (2574 * 256 + 44 * limit + 274) + 6 * limit + 20000 +
    401322 + 14226 + 149241 + 7273 + 1810 + 2 * queries + 8 + 2 ^ 30 +
    queries * (2574 * 256 + 44 * limit + 4447)

/-- The block sum is quadratic in the total external query count. -/
theorem compiledBlockAllowance_expanded (queries : Nat) :
    compiledBlockAllowance queries =
      44 * queries ^ 2 + 92224347 * queries + 48161862505799 := by
  unfold compiledBlockAllowance
  ring

/-- The rounded concrete polynomial covers the complete block sum. -/
theorem compiledBlockAllowance_bound (queries : Nat) :
    compiledBlockAllowance queries ≤ 64 * queries ^ 2 + 2 ^ 27 * queries + 2 ^ 46 := by
  rw [compiledBlockAllowance_expanded]
  apply Nat.add_le_add
  · apply Nat.add_le_add
    · exact Nat.mul_le_mul_right _ (by decide : 44 ≤ 64)
    · exact Nat.mul_le_mul_right _ (by norm_num : 92224347 ≤ 2 ^ 27)
  · norm_num

/-- The public request allowance uses the same maximum table count. -/
theorem recordedPublicHandler_allowance (queries count overlayCount : Nat) (memory : Memory)
    (request : Cryptography.PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool)
    (baseBound : count ≤ queries + 915671) (overlayBound : overlayCount ≤ queries + 915671) :
    recordedPublicHandlerReserve 256 count overlayCount memory request rest ≤
      2574 * 256 + 44 * (queries + 915671) + 4447 := by
  have bound := recordedPublicHandler_budget 256 count overlayCount memory request rest
  change 1809 + 1 + _ ≤ _ at bound
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
