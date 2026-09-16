import Proof.ConditionalDisclosureScheduleBridge
import Proof.ConditionalDisclosureKeySource

namespace Kriterion.ConditionalDisclosure.CurveSource

open BN254 Cryptography ArgoMAC ArgoMAC.Security
noncomputable section

def selectedLifts (source : CurveMaskSample) : Gate → FullHashLift :=
  fun gate => goodHashLiftSource (field source gate, source.2.2 gate.1 gate.2)

/-- Matching the actual selected curve program supplies every active raw-source
equation used by the real hidden-label count. -/
theorem reference_active (bridge mask : BaseField) (source : CurveMaskSample)
    (inputKey : InputMacKey) (input : AffineInput)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (matching : PermutationTranscriptMatches oracle (gateProgramRecords
      ((curveMaskSampleGarble bridge mask input source).request.schedule input (inputKey.encodeAffine input)))) :
    ∀ index, rawSlotBranch index.slot = circuitBucketInputBit input (rawLabelBucket index) →
      ∀ use : RawBucketUse (prescription source inputKey (selectedLifts source)) index,
        oracle.permutation index
          (circuitBucketInputLabel (inputKey.encodeAffine input) (inputKey.encodeAffine input) (rawLabelBucket index) ^^^
            rawBucketTweak (prescription source inputKey (selectedLifts source)) index use) =
          rawBucketOffset (prescription source inputKey (selectedLifts source)) index use ^^^
            circuitBucketInputLabel (inputKey.encodeAffine input) (inputKey.encodeAffine input) (rawLabelBucket index) := by
  intro index selected use
  rcases use with ⟨⟨gate, slot⟩, bucket⟩
  change fixedKeyIndex (location gate) gate.2.val slot = index at bucket
  subst index
  change rawSlotBranch slot = _ at selected
  let curve := (curveMaskSampleGarble bridge mask input source).request
  let directive := curve.actualDirective input (inputKey.encodeAffine input) gate.1 gate.2
  have bit : directive.bit = circuitBucketInputBit input
      (rawLabelBucket (fixedKeyIndex (location gate) gate.2.val slot)) := by
    rcases gate with ⟨adaptor, position⟩
    fin_cases adaptor <;>
      simp [directive, CurveGateRequest.actualDirective, actualDigitDirective,
        circuitBucketInputBit, rawLabelBucket, fixedKeyIndex, location, adaptorEquiv,
        Pipeline.FixedKeyLocation.kind, Nat.mod_eq_of_lt position.isLt]
  have active : rawSlotBranch slot = directive.bit := selected.trans bit.symm
  have member : directive.slotRecord slot ∈ gateProgramRecords
      (curve.schedule input (inputKey.encodeAffine input)) := by
    simp only [gateProgramRecords, List.mem_flatMap, List.mem_reverse,
      CurveGateRequest.mem_schedule_iff, GateDirective.mem_programRecords_iff]
    exact ⟨directive, ⟨gate.1, gate.2, rfl⟩, slot, active, rfl⟩
  have record := curve_actualDirective_record_eq_prescription bridge mask input source inputKey gate slot active
  change directive.slotRecord slot =
    (prescription source inputKey (selectedLifts source) gate).slotRecord slot at record
  have answer := matching (directive.slotRecord slot) member
  rw [record] at answer
  have label : (prescription source inputKey (selectedLifts source) gate).label slot =
      circuitBucketInputLabel (inputKey.encodeAffine input) (inputKey.encodeAffine input)
        (rawLabelBucket (fixedKeyIndex (location gate) gate.2.val slot)) := by
    calc
      _ = BitAdaptor.encode (key inputKey gate) (rawSlotBranch slot) := by cases slot <;> rfl
      _ = sourceLabels inputKey (rawLabelBucket (fixedKeyIndex (location gate) gate.2.val slot))
          (rawSlotBranch slot) := (sourceLabels_gate inputKey gate (rawSlotBranch slot)).symm
      _ = circuitSourceLabels inputKey inputKey
          (rawLabelBucket (fixedKeyIndex (location gate) gate.2.val slot))
          (circuitBucketInputBit input (rawLabelBucket (fixedKeyIndex (location gate) gate.2.val slot))) := by
        rw [selected]
        rfl
      _ = _ := circuitSourceLabels_selected inputKey inputKey input _
  change oracle.permutation (fixedKeyIndex (location gate) gate.2.val slot)
      ((prescription source inputKey (selectedLifts source) gate).label slot ^^^ (location gate).tweak) =
        (prescription source inputKey (selectedLifts source) gate).offset slot ^^^
          (prescription source inputKey (selectedLifts source) gate).label slot at answer
  rw [label] at answer
  exact answer

end
end Kriterion.ConditionalDisclosure.CurveSource
