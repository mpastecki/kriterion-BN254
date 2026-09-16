import Proof.ConditionalDisclosureCurve
import Proof.Privacy.Collision.AdaptiveLabelCollision

namespace Kriterion.DirectDisclosure.LabelCollision

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] publicInputMacKeyFintype Classical.propDecidable
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

private def xorEquiv (shift : Block) : Block ≃ Block where
  toFun value := value ^^^ shift
  invFun value := value ^^^ shift
  left_inv value := by dsimp; rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  right_inv value := by dsimp; rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- Every fixed shifted source label has exactly one inverse-block mass. -/
theorem shifted_label_mass [Fintype Block] (wire : EncPRF.PermutationIndex) (bit : Bool)
    (shift value : Block) :
    (PMF.uniformOfFintype InputMacKey).toOuterMeasure
      {key | inputKeyLabel key wire bit ^^^ shift = value} =
        (Fintype.card Block : ℝ≥0∞)⁻¹ := by
  have law : (PMF.uniformOfFintype InputMacKey).map
      (fun key => inputKeyLabel key wire bit ^^^ shift) = PMF.uniformOfFintype Block := by
    calc
      _ = ((PMF.uniformOfFintype InputMacKey).map (fun key => inputKeyLabel key wire bit)).map
          (xorEquiv shift) := by rw [PMF.map_comp]; rfl
      _ = _ := by rw [uniform_inputKeyLabel, map_uniformOfFintype_equivBetween]
  have mass := congrArg (fun distribution : PMF Block => distribution.toOuterMeasure {value}) law
  rw [PMF.toOuterMeasure_map_apply] at mass
  simpa only [Set.preimage, Set.mem_singleton_iff, PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply] using mass

/-- A single prescribed gate can conflict with either coordinate of a prior pair. -/
theorem one_use_mass_le [Fintype Block] (use : PrequeryLabelUse)
    (record : PermutationRecord Pipeline.FixedKeyIndex Block) :
    (PMF.uniformOfFintype InputMacKey).toOuterMeasure
      {key | inputKeyLabel key use.index use.bit ^^^ use.domainShift = record.domain ∨
        inputKeyLabel key use.index use.bit ^^^ use.rangeShift = record.range} ≤
      2 / (Fintype.card Block : ℝ≥0∞) := by
  calc
    _ ≤ (PMF.uniformOfFintype InputMacKey).toOuterMeasure
        {key | inputKeyLabel key use.index use.bit ^^^ use.domainShift = record.domain} +
      (PMF.uniformOfFintype InputMacKey).toOuterMeasure
        {key | inputKeyLabel key use.index use.bit ^^^ use.rangeShift = record.range} :=
      MeasureTheory.measure_union_le _ _
    _ = _ := by rw [shifted_label_mass, shifted_label_mass, div_eq_mul_inv, two_mul]

abbrev SlotUse := ConditionalDisclosure.CurveSource.Gate × Pipeline.FixedKeySlot

def GridCollision (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (uses : SlotUse → PrequeryLabelUse) (key : InputMacKey) : Prop :=
  ∃ query : Fin history.length, ∃ slot,
    let use := uses slot
    inputKeyLabel key use.index use.bit ^^^ use.domainShift = (history.get query).domain ∨
      inputKeyLabel key use.index use.bit ^^^ use.rangeShift = (history.get query).range

/-- This conservative union includes every curve gate/slot; no independence between
reused coordinate labels is asserted or needed. -/
theorem grid_collision_mass_le [Fintype Block]
    (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (uses : SlotUse → PrequeryLabelUse) :
    (PMF.uniformOfFintype InputMacKey).toOuterMeasure {key | GridCollision history uses key} ≤
      (12700 * history.length : Nat) / (Fintype.card Block : ℝ≥0∞) := by
  let event : (Fin history.length × SlotUse) → Set InputMacKey := fun pair =>
    {key | inputKeyLabel key (uses pair.2).index (uses pair.2).bit ^^^
        (uses pair.2).domainShift = (history.get pair.1).domain ∨
      inputKeyLabel key (uses pair.2).index (uses pair.2).bit ^^^
        (uses pair.2).rangeShift = (history.get pair.1).range}
  have events : {key | GridCollision history uses key} = ⋃ pair, event pair := by
    ext key
    simp only [GridCollision, Set.mem_setOf_eq, Set.mem_iUnion, Prod.exists, event]
  rw [events]
  have bound := finiteBadEventUnionMass_le (PMF.uniformOfFintype InputMacKey).toOuterMeasure
    event (2 / (Fintype.card Block : ℝ≥0∞)) (fun pair => one_use_mass_le (uses pair.2) (history.get pair.1))
  have slots : Fintype.card SlotUse = 6350 := by
    rw [Fintype.card_prod, ConditionalDisclosure.CurveSource.gate_card]
    have five : Fintype.card Pipeline.FixedKeySlot = 5 := by decide
    rw [five]
  apply bound.trans_eq
  rw [Fintype.card_prod, Fintype.card_fin, slots]
  push_cast
  simp only [div_eq_mul_inv]
  ring

/-- The fixed-query history grows by at most the declared public query budget. -/
theorem fixed_history_length {Result : Type*} {budget : Nat}
    (program : OracleProgram Garbling.oracleSpec Result budget) (state : SimulatorState)
    (output : Result × SimulatorState) (member : output ∈ (program.run idealOracleHandler state).support) :
    output.2.fixedTranscript.length ≤ state.fixedTranscript.length + budget := by
  induction program generalizing state with
  | pure distribution =>
    rw [OracleProgram.run_pure, PMF.mem_support_map_iff] at member
    obtain ⟨result, _, equal⟩ := member
    cases equal
    exact Nat.le_add_right _ _
  | query request next ih =>
    rw [OracleProgram.run_query] at member
    have bound := ih (idealOracleHandler request state).1 (idealOracleHandler request state).2 member
    have step : (idealOracleHandler request state).2.fixedTranscript.length ≤ state.fixedTranscript.length + 1 := by
      cases request <;> simp [idealOracleHandler, oracleHandlerFor, recordFixed, recordEnc, recordHash]
    omega
  | sample distribution next ih =>
    rw [OracleProgram.run_sample, PMF.mem_support_bind_iff] at member
    obtain ⟨value, _, member⟩ := member
    exact ih value state member

end
end Kriterion.DirectDisclosure.LabelCollision
