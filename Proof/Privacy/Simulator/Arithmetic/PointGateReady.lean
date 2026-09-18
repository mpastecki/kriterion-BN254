import Proof.Privacy.Simulator.Arithmetic.PointGateMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SharedSimulatorMachine
noncomputable section

/-- Exact point records and linked labels establish the complete point-loop invariant. -/
theorem pointGateMemory_ready [FieldCertificate]
    (attempts limit : Nat) (rows : Fin 92 → RowPublicSample) (input : AffineInput)
    (target : Fin 92 → Fin 3 → BaseField) (memory : Memory) (mac : InputMac) (requests : PointGateRequests)
    (state : SharedOracleSource)
    (stored : PointGateMemory rows input target memory.ram (memory.registers 11))
    (requestsAt : ∀ row, requests.get row = ⟨(rows row).x.request.retarget input (target row 0),
      (rows row).y.request.retarget input (target row 1), (rows row).z.request.retarget input (target row 2)⟩)
    (coordinates : memory.ram (memory.registers 12) = BitVec.ofNat 256 input.x.val ∧
      memory.ram (memory.registers 12 + 1) = BitVec.ofNat 256 input.y.val)
    (labels : WordsAt memory.ram (memory.registers 14) 0 ((encLinkMacWords mac).map (fun label => label.setWidth 256)))
    (sourcePointer : memory.registers 11 = BitVec.ofNat 256 privateBase)
    (inputPointer : memory.registers 12 = BitVec.ofNat 256 onlineInputBase)
    (labelPointer : memory.registers 14 = BitVec.ofNat 256 onlineLinkedBase)
    (represented : SharedSourceMemory memory state limit)
    (room : 256 + 2 * (limit + 3 * 303784) < 2 ^ 110) :
    GateLoopCoupledReady pointGatePlan
      (fun gate => sharedDirectiveSlot (pointDirectiveAt requests input mac gate))
      (fun gate => !(pointDirectiveAt requests input mac gate).bit)
      attempts 303784 0 limit memory state := by
  have data := stored.plan rows input target memory mac requests requestsAt coordinates labels
  apply gateLoopCoupledReady_typed pointGatePlan _ (fun index => Classical.choose (data index))
    attempts 303784 0 limit memory memory state (by decide) (GatePrivateAgreement.refl _) represented room
  · intro index
    exact Classical.choose_spec (data index)
  · intro index
    simpa only [pointGatePlan, Vector.getElem_ofFn] using pointGateCode_private memory
      ⟨index.val / 3302, by have bound := index.isLt; omega⟩
      ⟨index.val % 3302 / 254, by omega⟩ ⟨index.val % 254, by omega⟩
      onlineLinkedBase sourcePointer inputPointer labelPointer (by decide) (by decide)

/-- The fixed private point region stays exact after a private-frame update. -/
theorem PointGateMemory.privateFrame (rows : Fin 92 → RowPublicSample) (input : AffineInput)
    (target : Fin 92 → Fin 3 → BaseField) (ram next : Word → Word)
    (stored : PointGateMemory rows input target ram (BitVec.ofNat 256 privateBase))
    (same : ∀ cell, privateBase ≤ cell → cell < privateBase + 913657 →
      next (BitVec.ofNat 256 cell) = ram (BitVec.ofNat 256 cell)) :
    PointGateMemory rows input target next (BitVec.ofNat 256 privateBase) := by
  apply stored.congr rows input target ram next (BitVec.ofNat 256 privateBase)
  intro offset lower upper
  rw [← BitVec.ofNat_add]
  exact same (privateBase + offset) (by omega) (by omega)

end
end Kriterion.ArgoMAC.ArithmeticSimulator
