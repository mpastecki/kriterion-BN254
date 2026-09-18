import Proof.Privacy.Simulator.Arithmetic.PointGateTyped
import Proof.Privacy.Simulator.Arithmetic.OnlinePreparedPointRecords
import Proof.Privacy.Simulator.Arithmetic.GatePrivateBounds

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SimulatorSampling

/-- The point gate memory contains the three retargeted records in each row. -/
def PointGateMemory (rows : Fin 92 → RowPublicSample) (input : AffineInput)
    (target : Fin 92 → Fin 3 → BaseField) (ram : Word → Word) (pointer : Word) : Prop :=
  ∀ row : Fin 92,
    RetargetedGateMemory ((rows row).x.coefficients, (rows row).x.tables, (rows row).x.quotients, (rows row).x.targets)
      3 (((rows row).x.request.retarget input (target row 0)).x9Targets 0) ram pointer (1017 + 9920 * row.val + 6867) ∧
    RetargetedGateMemory ((rows row).y.coefficients, (rows row).y.tables, (rows row).y.quotients, (rows row).y.targets)
      3 (((rows row).y.request.retarget input (target row 1)).x9Targets 0) ram pointer (1017 + 9920 * row.val + 3815) ∧
    RetargetedGateMemory ((rows row).z.coefficients, (rows row).z.tables, (rows row).z.quotients, (rows row).z.targets)
      4 (((rows row).z.request.retarget input (target row 2)).x9Targets 0) ram pointer (1017 + 9920 * row.val)

/-- A memory update that preserves the point region retains all point records. -/
theorem PointGateMemory.congr (rows : Fin 92 → RowPublicSample) (input : AffineInput)
    (target : Fin 92 → Fin 3 → BaseField) (ram next : Word → Word) (pointer : Word)
    (stored : PointGateMemory rows input target ram pointer)
    (same : ∀ offset, 1017 ≤ offset → offset < 913657 →
      next (pointer + BitVec.ofNat 256 offset) = ram (pointer + BitVec.ofNat 256 offset)) :
    PointGateMemory rows input target next pointer := by
  intro row
  have bound := row.isLt
  refine ⟨(stored row).1.congr _ _ _ _ _ _ _ ?_,
    (stored row).2.1.congr _ _ _ _ _ _ _ ?_, (stored row).2.2.congr _ _ _ _ _ _ _ ?_⟩
  all_goals intro offset inside; apply same <;> omega

/-- The full point memory gives every flattened point descriptor its exact directive. -/
theorem PointGateMemory.plan (rows : Fin 92 → RowPublicSample) (input : AffineInput)
    (target : Fin 92 → Fin 3 → BaseField) (memory : Memory) (mac : InputMac) (requests : PointGateRequests)
    (stored : PointGateMemory rows input target memory.ram (memory.registers 11))
    (requestsAt : ∀ row, requests.get row = ⟨(rows row).x.request.retarget input (target row 0),
      (rows row).y.request.retarget input (target row 1), (rows row).z.request.retarget input (target row 2)⟩)
    (coordinates : memory.ram (memory.registers 12) = BitVec.ofNat 256 input.x.val ∧
      memory.ram (memory.registers 12 + 1) = BitVec.ofNat 256 input.y.val)
    (labels : WordsAt memory.ram (memory.registers 14) 0 ((encLinkMacWords mac).map (fun label => label.setWidth 256)))
    (index : Fin 303784) :
    ∃ quotient, GateTypedData memory pointGatePlan[index.val] (pointDirectiveAt requests input mac index) quotient := by
  let row : Fin 92 := ⟨index.val / 3302, by have bound := index.isLt; omega⟩
  let gate : Fin 13 := ⟨index.val % 3302 / 254, by omega⟩
  let bit : Fin 254 := ⟨index.val % 254, by omega⟩
  have result := pointGateCode_typed (rows row) input (target row) mac memory row coordinates labels
    (stored row).1 (stored row).2.1 (stored row).2.2 gate bit
  simpa only [pointGatePlan, Vector.getElem_ofFn, pointDirectiveAt, requestsAt] using result

end Kriterion.ArgoMAC.ArithmeticSimulator
