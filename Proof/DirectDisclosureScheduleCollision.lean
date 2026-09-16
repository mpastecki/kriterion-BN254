import Proof.DirectDisclosureLabelCollision
import Proof.Privacy.Programming.ActualScheduleRecords

namespace Kriterion.DirectDisclosure.LabelCollision

open BN254 Cryptography ArgoMAC ArgoMAC.Security
noncomputable section

private def dummyMac : InputMac := defaultSimulatorCoin.inputKey.encodeAffine ⟨0, 0⟩

private def slotBlock (directive : GateDirective) : Pipeline.FixedKeySlot → Block
  | .hash index => liftHashBlocks directive.lift.1 index
  | .pad index => targetPadBlocks directive.table directive.target index

/-- Its two shifts depend only on the selected request and input, never the label key. -/
def selectedUses (request : CurveGateRequest) (input : AffineInput) (slot : SlotUse) : PrequeryLabelUse :=
  let directive := request.actualDirective input dummyMac slot.1.1 slot.1.2
  ⟨circuitGateWire (.inl slot.1), directive.bit, directive.location.tweak,
    slotBlock directive slot.2⟩

private theorem directive_label (request : CurveGateRequest) (input : AffineInput)
    (key : InputMacKey) (gate : ConditionalDisclosure.CurveSource.Gate) :
    (request.actualDirective input (key.encodeAffine input) gate.1 gate.2).label =
      inputKeyLabel key (circuitGateWire (.inl gate))
        (request.actualDirective input dummyMac gate.1 gate.2).bit := by
  rcases gate with ⟨adaptor, bit⟩
  fin_cases adaptor <;>
    simp [CurveGateRequest.actualDirective, actualDigitDirective, InputMacKey.encodeAffine,
      InputMacKey.encode, encodeCoordinate, BitInput.ofAffine, inputKeyLabel, circuitGateWire,
      coordinateValues, Vector.get_eq_getElem]

/-- The grid's shifted source labels are the actual programmed domain and range. -/
theorem selectedUses_record (request : CurveGateRequest) (input : AffineInput)
    (key : InputMacKey) (slot : SlotUse) :
    let use := selectedUses request input slot
    let record := (request.actualDirective input (key.encodeAffine input) slot.1.1 slot.1.2).slotRecord slot.2
    inputKeyLabel key use.index use.bit ^^^ use.domainShift = record.domain ∧
      inputKeyLabel key use.index use.bit ^^^ use.rangeShift = record.range := by
  have label := directive_label request input key slot.1
  have location : (request.actualDirective input (key.encodeAffine input) slot.1.1 slot.1.2).location =
      (request.actualDirective input dummyMac slot.1.1 slot.1.2).location := by
    rcases slot with ⟨⟨adaptor, bit⟩, which⟩
    fin_cases adaptor <;>
      simp only [CurveGateRequest.actualDirective, actualDigitDirective,
        Matrix.cons_val_zero', Matrix.cons_val_succ']
  have block : slotBlock (request.actualDirective input (key.encodeAffine input) slot.1.1 slot.1.2) slot.2 =
      slotBlock (request.actualDirective input dummyMac slot.1.1 slot.1.2) slot.2 := by
    rcases slot with ⟨⟨adaptor, bit⟩, which⟩
    fin_cases adaptor <;> cases which <;>
      simp [slotBlock, CurveGateRequest.actualDirective, actualDigitDirective]
  change _ = _ ∧ _ = _
  dsimp only [selectedUses, GateDirective.slotRecord, fixedProgramRecord, gateInput]
  constructor
  · rw [label, location]
  · change _ = slotBlock _ slot.2 ^^^ _
    rw [label, block, BitVec.xor_comm]

/-- Avoiding the independent-key grid excludes every actual selected-program
collision with the complete prior fixed-query history, in either direction. -/
theorem selected_schedule_fresh (request : CurveGateRequest) (input : AffineInput)
    (key : InputMacKey) (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (good : ¬ GridCollision history (selectedUses request input) key) :
    ∀ record ∈ gateProgramRecords (request.schedule input (key.encodeAffine input)),
      FreshPermutationPair history record.index record.domain record.range := by
  intro record member
  simp only [gateProgramRecords, List.mem_flatMap, List.mem_reverse] at member
  obtain ⟨directive, directiveMember, recordMember⟩ := member
  obtain ⟨adaptor, bit, rfl⟩ := (request.mem_schedule_iff input (key.encodeAffine input) directive).mp directiveMember
  obtain ⟨slot, _, rfl⟩ := (GateDirective.mem_programRecords_iff _ record).mp recordMember
  intro prior priorMember _
  obtain ⟨index, equal⟩ := List.mem_iff_get.mp priorMember
  subst prior
  have coordinates := selectedUses_record request input key ((adaptor, bit), slot)
  constructor
  · intro collision
    apply good
    exact ⟨index, ((adaptor, bit), slot), Or.inl (coordinates.1.trans collision.symm)⟩
  · intro collision
    apply good
    exact ⟨index, ((adaptor, bit), slot), Or.inr (coordinates.2.trans collision.symm)⟩

end
end Kriterion.DirectDisclosure.LabelCollision
