import Proof.ConditionalDisclosureCurveRatio
import Proof.Privacy.Source.ActualKeyMass

namespace Kriterion.ConditionalDisclosure.CurveSource

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- The source uses only the actual input key; no independent point key is introduced. -/
def sourceLabels (inputKey : InputMacKey) (bucket : RawLabelBucket) (branch : Bool) : Block :=
  inputKeyLabel inputKey (circuitBucketWire bucket) branch

theorem sourceLabels_gate (inputKey : InputMacKey) (gate : Gate) (branch : Bool) :
    sourceLabels inputKey (rawLabelBucket (fixedKeyIndex (location gate) gate.2.val (.hash 0))) branch =
      BitAdaptor.encode (key inputKey gate) branch := by
  rcases gate with ⟨adaptor, bit⟩
  fin_cases adaptor <;>
    simp [sourceLabels, circuitBucketWire, key, location, adaptorEquiv, rawLabelBucket,
      fixedKeyIndex, Pipeline.FixedKeyLocation.kind, Nat.mod_eq_of_lt bit.isLt, inputKeyLabel]

theorem relabel_prescription (source : CurveMaskSample) (baseKey inputKey : InputMacKey)
    (lifts : Gate → FullHashLift) :
    rawGatesWithLabels (prescription source baseKey lifts) (sourceLabels inputKey) =
      prescription source inputKey lifts := by
  funext gate
  simp only [rawGatesWithLabels, prescription]
  rw [sourceLabels_gate, sourceLabels_gate]
  rfl

private theorem coordinateLabel_bucket (mac : InputMac) (bucket : RawLabelBucket) :
    inputMacCoordinateEquiv mac (circuitBucketWire bucket) = circuitBucketInputLabel mac mac bucket := by
  rcases bucket with ⟨kind, position⟩
  cases kind with
  | curve adaptor => cases adaptor <;> rfl
  | point coordinate adaptor => cases coordinate <;> cases adaptor <;> rfl

def decodedKey (input : AffineInput) (mac : InputMac)
    (hidden : EncPRF.PermutationIndex → Block) : InputMacKey :=
  (selectedKeyLabelsEquiv (inputSelectedLabelBit input)).symm (inputMacCoordinateEquiv mac, hidden)

/-- The preserved label fiber is exactly the actual encoding of the selected affine input. -/
theorem decodedKey_labels (input : AffineInput) (mac : InputMac)
    (hidden : EncPRF.PermutationIndex → Block) : (decodedKey input mac hidden).encodeAffine input = mac := by
  apply (selectedKeyLabels_public_iff input _ mac).mp
  exact congrArg Prod.fst ((selectedKeyLabelsEquiv (inputSelectedLabelBit input)).apply_symm_apply
    (inputMacCoordinateEquiv mac, hidden))

/-- The shared hidden-label source is the actual remaining half of this same input key. -/
theorem mixedLabels_eq_source (input : AffineInput) (mac : InputMac)
    (hidden : EncPRF.PermutationIndex → Block) :
    rawMixedLabels (circuitBucketInputBit input) (circuitBucketInputLabel mac mac)
      circuitBucketWire (fun _ => 0) hidden = sourceLabels (decodedKey input mac hidden) := by
  funext bucket branch
  simp only [rawMixedLabels, BitVec.xor_zero, circuitBucketInputBit_wire,
    ← coordinateLabel_bucket]
  change (if branch = inputSelectedLabelBit input (circuitBucketWire bucket)
    then inputMacCoordinateEquiv mac (circuitBucketWire bucket) else hidden (circuitBucketWire bucket) ^^^ (0 : Block)) =
    (inputKeyLabelEquiv (inputKeyLabelEquiv.symm (fun index selected =>
      if selected = inputSelectedLabelBit input index then inputMacCoordinateEquiv mac index else hidden index)))
      (circuitBucketWire bucket) branch
  rw [Equiv.apply_symm_apply]
  have zero : hidden (circuitBucketWire bucket) ^^^ (0 : Block) = hidden (circuitBucketWire bucket) :=
    BitVec.xor_zero
  exact congrArg (fun value : Block =>
    if branch = inputSelectedLabelBit input (circuitBucketWire bucket)
    then inputMacCoordinateEquiv mac (circuitBucketWire bucket) else value)
    zero

theorem mixed_prescription_eq (source : CurveMaskSample) (baseKey : InputMacKey)
    (lifts : Gate → FullHashLift) (input : AffineInput) (mac : InputMac)
    (hidden : EncPRF.PermutationIndex → Block) :
    rawGatesWithLabels (prescription source baseKey lifts)
      (rawMixedLabels (circuitBucketInputBit input) (circuitBucketInputLabel mac mac)
        circuitBucketWire (fun _ => 0) hidden) =
      prescription source (decodedKey input mac hidden) lifts := by
  rw [mixedLabels_eq_source, relabel_prescription]

/-- The selected-label fiber factors the ACTUAL full curve source and complete real
oracle transcript. The only remaining labels are one hidden128-bit value per input wire. -/
theorem actual_source_key_mass [Fintype Block]
    (bridge mask r1 r2 : BaseField) (source : CurveMaskSample) (lifts : Gate → FullHashLift)
    (randomizers : source.1.1 = ![r1, r2])
    (residues : ∀ gate, field source gate = ((lifts gate).val : BaseField))
    (input : AffineInput) (mac : InputMac) (randomness : Garbling.Randomness)
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) :
    (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
      {sample | sample.2.encodeAffine input = mac ∧
        actual bridge mask r1 r2 sample.1 sample.2 = (lifts, table source) ∧
        OracleTranscriptCompatible Garbling.oracleHandler
          {randomness with fixedKeyOracle := sample.1} transcript} =
    (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ *
      (PMF.uniformOfFintype
        ((PermutationOracle Pipeline.FixedKeyIndex Block) × (EncPRF.PermutationIndex → Block))).toOuterMeasure
          {sample | RawGarblingMatches (prescription source (decodedKey input mac sample.2) lifts) sample.1 ∧
            OracleTranscriptCompatible Garbling.oracleHandler
              {randomness with fixedKeyOracle := sample.1} transcript} := by
  let event : Set ((PermutationOracle Pipeline.FixedKeyIndex Block) × (EncPRF.PermutationIndex → Block)) :=
    {sample | RawGarblingMatches (prescription source (decodedKey input mac sample.2) lifts) sample.1 ∧
      OracleTranscriptCompatible Garbling.oracleHandler {randomness with fixedKeyOracle := sample.1} transcript}
  have factor := uniform_key_event_mass (selectedKeyLabelsEquiv (inputSelectedLabelBit input))
    (inputMacCoordinateEquiv mac) event
  rw [← factor]
  congr 1
  ext sample
  simp only [Set.mem_setOf_eq]
  rw [← selectedKeyLabels_public_iff input sample.2 mac]
  apply and_congr_right
  intro selected
  have decoded : decodedKey input mac ((selectedKeyLabelsEquiv (inputSelectedLabelBit input) sample.2).2) =
      sample.2 := by
    unfold decodedKey
    rw [← selected]
    exact (selectedKeyLabelsEquiv (inputSelectedLabelBit input)).symm_apply_apply sample.2
  simp only [event, Set.mem_setOf_eq, decoded]
  exact and_congr_left (fun _ => actual_fiber bridge mask r1 r2 sample.1 sample.2 source lifts randomizers residues)

end
end Kriterion.ConditionalDisclosure.CurveSource
