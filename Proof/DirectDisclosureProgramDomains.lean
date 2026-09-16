import Proof.ConditionalDisclosureCurve
import Proof.Privacy.Programming.ActualScheduleRecords
import Proof.Privacy.Source.AdaptivePermutationRatio

namespace Kriterion.ConditionalDisclosure.CurveSource

open BN254 Cryptography ArgoMAC ArgoMAC.Security
noncomputable section
attribute [local instance] rawBucketUseFintype fixedQueryDomainFintype

private def directive (curve : CurveGateRequest) (input : AffineInput) (mac : InputMac)
    (gate : Gate) : GateDirective := curve.actualDirective input mac gate.1 gate.2

private theorem directive_index (curve : CurveGateRequest) (input : AffineInput) (mac : InputMac)
    (gate : Gate) (slot : Pipeline.FixedKeySlot) :
    ((directive curve input mac gate).slotRecord slot).index =
      fixedKeyIndex (location gate) gate.2.val slot := by
  rcases gate with ⟨adaptor, bit⟩
  fin_cases adaptor <;> rfl

private theorem directive_location (curve : CurveGateRequest) (input : AffineInput) (mac : InputMac)
    (gate : Gate) : (directive curve input mac gate).location = location gate := by
  rcases gate with ⟨adaptor, bit⟩
  fin_cases adaptor <;> rfl

private theorem directive_bit (curve : CurveGateRequest) (input : AffineInput) (mac : InputMac)
    (gate : Gate) (slot : Pipeline.FixedKeySlot) :
    (directive curve input mac gate).bit = circuitBucketInputBit input
      (rawLabelBucket (fixedKeyIndex (location gate) gate.2.val slot)) := by
  rcases gate with ⟨adaptor, bit⟩
  fin_cases adaptor <;>
    simp [directive, CurveGateRequest.actualDirective, actualDigitDirective,
      circuitBucketInputBit, rawLabelBucket, fixedKeyIndex, location, adaptorEquiv,
      Pipeline.FixedKeyLocation.kind, Nat.mod_eq_of_lt bit.isLt]

private theorem directive_label (curve : CurveGateRequest) (input : AffineInput) (mac : InputMac)
    (gate : Gate) (slot : Pipeline.FixedKeySlot) :
    (directive curve input mac gate).label = circuitBucketInputLabel mac mac
      (rawLabelBucket (fixedKeyIndex (location gate) gate.2.val slot)) := by
  rcases gate with ⟨adaptor, bit⟩
  fin_cases adaptor <;>
    simp [directive, CurveGateRequest.actualDirective, actualDigitDirective,
      circuitBucketInputLabel, rawLabelBucket, fixedKeyIndex, location, adaptorEquiv,
      Pipeline.FixedKeyLocation.kind, Nat.mod_eq_of_lt bit.isLt]

private theorem mem_records (curve : CurveGateRequest) (input : AffineInput) (mac : InputMac)
    (record : PermutationRecord Pipeline.FixedKeyIndex Block) :
    record ∈ gateProgramRecords (curve.schedule input mac) ↔
      ∃ gate : Gate, ∃ slot, rawSlotBranch slot = (directive curve input mac gate).bit ∧
        (directive curve input mac gate).slotRecord slot = record := by
  simp only [gateProgramRecords, List.mem_flatMap, List.mem_reverse,
    CurveGateRequest.mem_schedule_iff, GateDirective.mem_programRecords_iff]
  constructor
  · rintro ⟨d, ⟨adaptor, bit, rfl⟩, slot, active, same⟩
    exact ⟨(adaptor, bit), slot, active, same⟩
  · rintro ⟨⟨adaptor, bit⟩, slot, active, same⟩
    exact ⟨_, ⟨adaptor, bit, rfl⟩, slot, active, same⟩

/-- The actual curve schedule has precisely the active domains of the curve-only source. -/
theorem program_domains (curve : CurveGateRequest) (input : AffineInput) (mac : InputMac)
    (source : CurveMaskSample) (inputKey : InputMacKey) (lifts : Gate → FullHashLift)
    (index : Pipeline.FixedKeyIndex) :
    programmedDomains (gateProgramRecords (curve.schedule input mac)) index =
      rawActiveDomains (prescription source inputKey lifts) (circuitBucketInputBit input)
        (circuitBucketInputLabel mac mac) index := by
  ext domain
  constructor
  · rintro ⟨record, member, sameIndex, sameDomain⟩
    rcases (mem_records curve input mac record).mp member with ⟨gate, slot, active, rfl⟩
    have bucket := (directive_index curve input mac gate slot).symm.trans sameIndex
    clear sameIndex
    subst index
    have selected := active.trans (directive_bit curve input mac gate slot)
    change rawSlotBranch (fixedKeyIndex (location gate) gate.2.val slot).slot = _ at selected
    rw [rawActiveDomains, if_pos selected]
    refine ⟨⟨(gate, slot), rfl⟩, ?_⟩
    change (directive curve input mac gate).label ^^^
      (directive curve input mac gate).location.tweak = domain at sameDomain
    rw [directive_label curve input mac gate slot, directive_location] at sameDomain
    exact sameDomain
  · intro member
    by_cases selected : rawSlotBranch index.slot = circuitBucketInputBit input (rawLabelBucket index)
    · rw [rawActiveDomains, if_pos selected] at member
      rcases member with ⟨⟨⟨gate, slot⟩, bucket⟩, sameDomain⟩
      change fixedKeyIndex (location gate) gate.2.val slot = index at bucket
      subst index
      have active : rawSlotBranch slot = (directive curve input mac gate).bit := by
        rw [directive_bit curve input mac gate slot]
        exact selected
      refine ⟨_, (mem_records curve input mac _).mpr ⟨gate, slot, active, rfl⟩,
        directive_index curve input mac gate slot, ?_⟩
      change (directive curve input mac gate).label ^^^
        (directive curve input mac gate).location.tweak = domain
      rw [directive_label curve input mac gate slot, directive_location]
      exact sameDomain
    · simp only [rawActiveDomains, if_neg selected, Set.mem_empty_iff_false] at member

/-- Selected indices contain the exact singleton-or-empty raw bucket count. -/
theorem program_domain_count [Fintype Block]
    (curve : CurveGateRequest) (input : AffineInput) (mac : InputMac)
    (source : CurveMaskSample) (inputKey : InputMacKey) (lifts : Gate → FullHashLift)
    (index : Pipeline.FixedKeyIndex) :
    Fintype.card (FixedQueryDomain (gateProgramRecords (curve.schedule input mac)) index) =
      if rawSlotBranch index.slot = circuitBucketInputBit input (rawLabelBucket index)
      then Fintype.card (RawBucketUse (prescription source inputKey lifts) index) else 0 := by
  classical
  let gates := prescription source inputKey lifts
  let domains := fun use : RawBucketUse gates index =>
    circuitBucketInputLabel mac mac (rawLabelBucket index) ^^^ rawBucketTweak gates index use
  have domainLaw := program_domains curve input mac source inputKey lifts index
  by_cases active : rawSlotBranch index.slot = circuitBucketInputBit input (rawLabelBucket index)
  · rw [if_pos active]
    rw [rawActiveDomains, if_pos active] at domainLaw
    let := bucket_subsingleton source inputKey lifts index
    have injective : Function.Injective domains := fun _ _ _ => Subsingleton.elim _ _
    have equivalence : FixedQueryDomain (gateProgramRecords (curve.schedule input mac)) index ≃
        RawBucketUse gates index :=
      (Equiv.setCongr domainLaw).trans (Equiv.ofInjective domains injective).symm
    exact Fintype.card_congr equivalence
  · rw [if_neg active]
    rw [rawActiveDomains, if_neg active] at domainLaw
    let : IsEmpty (FixedQueryDomain (gateProgramRecords (curve.schedule input mac)) index) :=
      ⟨fun value => by
        have member := value.property
        change value.val ∈ programmedDomains (gateProgramRecords (curve.schedule input mac)) index at member
        rw [domainLaw] at member
        exact member⟩
    exact Fintype.card_eq_zero

private theorem nodup_of_enumerates {Index Value : Type*} [Fintype Index]
    (values : List Value) (enumerate : Index → Value)
    (injective : Function.Injective enumerate)
    (members : ∀ value, value ∈ values ↔ ∃ index, enumerate index = value)
    (length : values.length = Fintype.card Index) : values.Nodup := by
  classical
  have equal : values.toFinset = Finset.univ.image enumerate := by
    ext value
    simp only [List.mem_toFinset, members, Finset.mem_image, Finset.mem_univ, true_and]
  have count : values.toFinset.card = values.length := by
    rw [equal, Finset.card_image_of_injective _ injective, Finset.card_univ, length]
  exact (Multiset.toFinset_card_eq_card_iff_nodup (m := (values : Multiset Value))).mp count

private theorem directive_injective (curve : CurveGateRequest) (input : AffineInput)
    (mac : InputMac) : Function.Injective (directive curve input mac) := by
  intro first second same
  have indices := congrArg (fun d : GateDirective => (d.slotRecord (.hash 0)).index) same
  rw [directive_index, directive_index] at indices
  exact congrArg Prod.fst (@index_injective (first, .hash 0) (second, .hash 0) indices)

/-- The curve schedule enumerates each physical gate once. -/
theorem schedule_nodup (curve : CurveGateRequest) (input : AffineInput) (mac : InputMac) :
    (curve.schedule input mac).Nodup := by
  apply nodup_of_enumerates _ (directive curve input mac) (directive_injective curve input mac)
  · intro value
    rw [CurveGateRequest.mem_schedule_iff]
    constructor
    · rintro ⟨adaptor, bit, same⟩
      exact ⟨(adaptor, bit), same⟩
    · rintro ⟨⟨adaptor, bit⟩, same⟩
      exact ⟨adaptor, bit, same⟩
  · rw [CurveGateRequest.schedule_length, gate_card]
    norm_num [coordinateBitCount]

private theorem directive_program_index_nodup (d : GateDirective) :
    (d.programRecords.map PermutationRecord.index).Nodup := by
  have injective : Function.Injective (fun slot => (d.slotRecord slot).index) := by
    intro first second same
    exact congrArg Pipeline.FixedKeyIndex.slot same
  unfold GateDirective.programRecords
  cases selected : d.bit
  · change (([.hash 2, .hash 1, .hash 0].map d.slotRecord).map PermutationRecord.index).Nodup
    rw [List.map_map]
    exact List.Nodup.map injective (by decide)
  · change (([.pad 1, .pad 0].map d.slotRecord).map PermutationRecord.index).Nodup
    rw [List.map_map]
    exact List.Nodup.map injective (by decide)

/-- All selected records use different permutation indices, eliminating internal batch collisions. -/
theorem program_indices_nodup (curve : CurveGateRequest) (input : AffineInput) (mac : InputMac) :
    ((gateProgramRecords (curve.schedule input mac)).map PermutationRecord.index).Nodup := by
  rw [gateProgramRecords, List.map_flatMap, List.nodup_flatMap]
  constructor
  · intro d _
    rw [List.map_reverse]
    exact List.nodup_reverse.mpr (directive_program_index_nodup d)
  · apply (schedule_nodup curve input mac).pairwise_of_forall_ne
    intro first firstMember second secondMember different
    apply List.disjoint_left.mpr
    intro index firstRecord secondRecord
    rcases (CurveGateRequest.mem_schedule_iff curve input mac first).mp firstMember with
      ⟨firstAdaptor, firstBit, rfl⟩
    rcases (CurveGateRequest.mem_schedule_iff curve input mac second).mp secondMember with
      ⟨secondAdaptor, secondBit, rfl⟩
    rcases List.mem_map.mp firstRecord with ⟨firstRecord, firstMember, firstIndex⟩
    rcases List.mem_map.mp secondRecord with ⟨secondRecord, secondMember, secondIndex⟩
    rcases (GateDirective.mem_programRecords_iff _ firstRecord).mp
      (List.mem_reverse.mp firstMember) with ⟨firstSlot, _, rfl⟩
    rcases (GateDirective.mem_programRecords_iff _ secondRecord).mp
      (List.mem_reverse.mp secondMember) with ⟨secondSlot, _, rfl⟩
    have indices := firstIndex.trans secondIndex.symm
    change ((directive curve input mac (firstAdaptor, firstBit)).slotRecord firstSlot).index =
      ((directive curve input mac (secondAdaptor, secondBit)).slotRecord secondSlot).index at indices
    rw [directive_index, directive_index] at indices
    have same := congrArg Prod.fst (@index_injective
      ((firstAdaptor, firstBit), firstSlot) ((secondAdaptor, secondBit), secondSlot) indices)
    exact different (congrArg (directive curve input mac) same)

end
end Kriterion.ConditionalDisclosure.CurveSource
