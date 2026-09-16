import Construction.ConditionalDisclosure
import Proof.Privacy.Programming.ActualGateConstraints

namespace Kriterion.ConditionalDisclosure.CurveSource

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section

attribute [local instance] bitAdaptorTableFintype

/-- The disclosure circuit contains only these1270 bit adaptors. -/
abbrev Gate := Fin 5 × Fin coordinateBitCount

def adaptorEquiv : Fin 5 ≃ Pipeline.CurveAdaptor where
  toFun index := ![.x3, .x5, .x7, .y4, .y6] index
  invFun adaptor := match adaptor with
    | .x3 => 0 | .x5 => 1 | .x7 => 2 | .y4 => 3 | .y6 => 4
  left_inv index := by fin_cases index <;> rfl
  right_inv adaptor := by cases adaptor <;> rfl

def location (gate : Gate) : Pipeline.FixedKeyLocation :=
  .curve (adaptorEquiv gate.1)

def key (inputKey : InputMacKey) (gate : Gate) : BitAdaptor.Key :=
  (![inputKey.x, inputKey.x, inputKey.x, inputKey.y, inputKey.y] gate.1).get gate.2

def field (source : CurveMaskSample) (gate : Gate) : BaseField :=
  source.1.2 gate.1 gate.2

def table (source : CurveMaskSample) (gate : Gate) : BitAdaptor.Table :=
  (source.2.1 gate.1).get gate.2

def slope (source : CurveMaskSample) (gate : Gate) : BaseField :=
  ![-source.1.1 0, -DigitAdaptor.fromBits (source.1.2 0),
    -DigitAdaptor.fromBits (source.1.2 1), -source.1.1 1,
    -DigitAdaptor.fromBits (source.1.2 3)] gate.1

def prescription (source : CurveMaskSample) (inputKey : InputMacKey)
    (lifts : Gate → FullHashLift) (gate : Gate) : RawGatePrescription := {
  location := location gate
  window := gate.2.val
  key := key inputKey gate
  slope := slope source gate
  lift := lifts gate
  table := table source gate }

def tablesOf (value : CurveMembership.Table) (gate : Gate) : BitAdaptor.Table :=
  (![value.x3, value.x5, value.x7, value.y4, value.y6] gate.1).get gate.2

/-- The actual source keeps every full false hash and every complete256-bit row. -/
abbrev FullSource := (Gate → FullHashLift) × (Gate → BitAdaptor.Table)

def actual (bridge mask r1 r2 : BaseField)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) (inputKey : InputMacKey) : FullSource :=
  ((fun gate => fixedDaviesMeyerHashLift (location gate) gate.2.val
      (key inputKey gate).falseLabel oracle),
    tablesOf (CurveMembership.garble bridge mask r1 r2 (Pipeline.curveOracles oracle) inputKey))

def maskSource (bridge mask r1 r2 : BaseField)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) (inputKey : InputMacKey)
    (quotients : Fin 5 → Fin coordinateBitCount → HashLiftQuotient) : CurveMaskSample :=
  actualCurveMaskSample bridge mask r1 r2 (Pipeline.curveOracles oracle) inputKey quotients

theorem actual_field (bridge mask r1 r2 : BaseField)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) (inputKey : InputMacKey)
    (quotients : Fin 5 → Fin coordinateBitCount → HashLiftQuotient) (gate : Gate) :
    field (maskSource bridge mask r1 r2 oracle inputKey quotients) gate =
      (Pipeline.fixedKeyGate oracle (location gate) gate.2.val).hashToField
        (key inputKey gate).falseLabel := by
  rcases gate with ⟨adaptor, bit⟩
  fin_cases adaptor <;> rfl

private theorem digit_table_get (windows : Nat → BitAdaptor.FixedKeyOracle)
    (slope : BaseField) (key : CoordinateMacKey) (bit : Fin coordinateBitCount) :
    ((DigitAdaptor.garble windows slope key).1).get bit =
      (BitAdaptor.garble (windows bit.val) slope (key.get bit)).1 := by
  simp [DigitAdaptor.garble]

/-- These are the actual triangular slopes and ciphertext rows, including offcurve inputs. -/
theorem actual_table (bridge mask r1 r2 : BaseField)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) (inputKey : InputMacKey)
    (quotients : Fin 5 → Fin coordinateBitCount → HashLiftQuotient) (gate : Gate) :
    let source := maskSource bridge mask r1 r2 oracle inputKey quotients
    table source gate =
      (BitAdaptor.garble (Pipeline.fixedKeyGate oracle (location gate) gate.2.val)
        (slope source gate) (key inputKey gate)).1 := by
  dsimp only
  rcases gate with ⟨adaptor, bit⟩
  fin_cases adaptor
  all_goals
    simp [table, slope, maskSource, actualCurveMaskSample, curveMaskSource,
      Pipeline.curveOracles, CurveMembership.garble, digitGarble_bitsK_eq,
      digit_table_get, location, adaptorEquiv, key]

private theorem data_of_hash (bridge mask r1 r2 : BaseField)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) (inputKey : InputMacKey)
    (source : CurveMaskSample) (lifts : Gate → FullHashLift)
    (randomizers : source.1.1 = ![r1, r2])
    (residues : ∀ gate, field source gate = ((lifts gate).val : BaseField))
    (hashes : ∀ gate, fixedDaviesMeyerHashLift (location gate) gate.2.val
      (key inputKey gate).falseLabel oracle = lifts gate) :
    (maskSource bridge mask r1 r2 oracle inputKey source.2.2).1 = source.1 := by
  apply Prod.ext
  · exact randomizers.symm
  · funext adaptor bit
    have equal := fixedHashToField_of_lift oracle (location (adaptor, bit)) bit.val
      (key inputKey (adaptor, bit)).falseLabel (lifts (adaptor, bit)) (hashes (adaptor, bit))
    exact (actual_field bridge mask r1 r2 oracle inputKey source.2.2 (adaptor, bit)).trans
      (equal.trans (residues (adaptor, bit)).symm)

/-- The complete curve source fiber equals its actual five-slot permutation constraints.
No point-MAC rows or independent point labels occur in this source. -/
theorem actual_fiber (bridge mask r1 r2 : BaseField)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) (inputKey : InputMacKey)
    (source : CurveMaskSample) (lifts : Gate → FullHashLift)
    (randomizers : source.1.1 = ![r1, r2])
    (residues : ∀ gate, field source gate = ((lifts gate).val : BaseField)) :
    actual bridge mask r1 r2 oracle inputKey = (lifts, table source) ↔
      RawGarblingMatches (prescription source inputKey lifts) oracle := by
  simp only [actual, Prod.mk.injEq]
  constructor
  · rintro ⟨hashes, tables⟩ gate
    have hash : ∀ gate, fixedDaviesMeyerHashLift (location gate) gate.2.val
        (key inputKey gate).falseLabel oracle = lifts gate := fun gate => congrFun hashes gate
    have data := data_of_hash bridge mask r1 r2 oracle inputKey source lifts randomizers residues hash
    refine ⟨hash gate, ?_⟩
    have row := actual_table bridge mask r1 r2 oracle inputKey source.2.2 gate
    have slopes : slope (maskSource bridge mask r1 r2 oracle inputKey source.2.2) gate =
        slope source gate := by simp only [slope, data]
    dsimp only at row
    rw [slopes] at row
    exact row.symm.trans (congrFun tables gate)
  · intro matching
    have hashes : ∀ gate, fixedDaviesMeyerHashLift (location gate) gate.2.val
        (key inputKey gate).falseLabel oracle = lifts gate := fun gate => (matching gate).1
    have data := data_of_hash bridge mask r1 r2 oracle inputKey source lifts randomizers residues hashes
    refine ⟨funext hashes, ?_⟩
    funext gate
    have row := actual_table bridge mask r1 r2 oracle inputKey source.2.2 gate
    have slopes : slope (maskSource bridge mask r1 r2 oracle inputKey source.2.2) gate =
        slope source gate := by simp only [slope, data]
    dsimp only at row
    rw [slopes] at row
    exact row.trans (matching gate).2

/-- Every curve bit/slot uses a different public permutation index. -/
theorem index_injective : Function.Injective (fun use : Gate × Pipeline.FixedKeySlot =>
    fixedKeyIndex (location use.1) use.1.2.val use.2) := by
  rintro ⟨⟨a, bit⟩, slot⟩ ⟨⟨b, bit'⟩, slot'⟩ equal
  have kinds := congrArg Pipeline.FixedKeyIndex.kind equal
  have bits := congrArg Pipeline.FixedKeyIndex.position equal
  have slots := congrArg Pipeline.FixedKeyIndex.slot equal
  have adaptors : adaptorEquiv a = adaptorEquiv b :=
    Pipeline.FixedKeyKind.curve.inj kinds
  have sameA := adaptorEquiv.injective adaptors
  have sameBit : bit = bit' := by
    apply Fin.ext
    simpa only [fixedKeyIndex, Nat.mod_eq_of_lt bit.isLt, Nat.mod_eq_of_lt bit'.isLt] using
      congrArg Fin.val bits
  cases sameA
  cases sameBit
  cases slots
  rfl

/-- Thus there is no within-bucket birthday event for this source. -/
theorem bucket_subsingleton (source : CurveMaskSample) (inputKey : InputMacKey)
    (lifts : Gate → FullHashLift) (index : Pipeline.FixedKeyIndex) :
    Subsingleton (RawBucketUse (prescription source inputKey lifts) index) := by
  constructor
  intro first second
  apply Subtype.ext
  exact index_injective (first.property.trans second.property.symm)

private def tableBlocksEquiv : BitAdaptor.Table ≃ (Fin 2 → Block) :=
  (show BitAdaptor.Table ≃ BitAdaptor.Ciphertext from
    ⟨BitAdaptor.Table.trueRow, fun row => ⟨row⟩, fun _ => rfl, fun _ => rfl⟩).trans ciphertextBlockEquiv

theorem gate_card : Fintype.card Gate = 1270 := by
  simp [Gate, coordinateBitCount]

/-- The full source contains exactly6350 independent block positions. -/
theorem fullSource_card [Fintype Block] :
    Fintype.card FullSource = Fintype.card Block ^ 6350 := by
  have hashes : Fintype.card FullHashLift = Fintype.card Block ^ 3 :=
    (Fintype.card_congr fullHashLiftBlockEquiv).trans (by rw [Fintype.card_fun, Fintype.card_fin])
  have tables : Fintype.card BitAdaptor.Table = Fintype.card Block ^ 2 :=
    (Fintype.card_congr tableBlocksEquiv).trans (by rw [Fintype.card_fun, Fintype.card_fin])
  simp only [FullSource, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, hashes, tables]
  rw [← pow_mul, ← pow_mul, ← pow_add]
  all_goals norm_num [coordinateBitCount]

end
end Kriterion.ConditionalDisclosure.CurveSource
