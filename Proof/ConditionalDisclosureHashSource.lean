import Proof.ConditionalDisclosureCurve
import Proof.Privacy.Distribution.HashDistribution

namespace Kriterion.ConditionalDisclosure.CurveSource

open BN254 Cryptography ArgoMAC ArgoMAC.Security
noncomputable section

attribute [local instance] bitAdaptorTableFintype publicVectorFintype curveMaskSampleFintype

/-- The actual two randomizers and all complete256-bit public rows are retained. -/
abbrev HashRest := (Fin 2 → BaseField) × (Gate → BitAdaptor.Table)

local instance : Nonempty HashRest := ⟨(fun _ => 0, fun _ => defaultBitAdaptorTable)⟩
local instance : Nonempty CurveMaskSample :=
  ⟨((fun _ => 0, fun _ _ => 0),
    (fun _ => Vector.replicate coordinateBitCount defaultBitAdaptorTable),
    fun _ _ => defaultHashLiftQuotient)⟩

/-- The source split keeps the full quotient tape and every actual curve randomizer. -/
def hashSplit : CurveMaskSample ≃ (Gate → BaseField × HashLiftQuotient) × HashRest where
  toFun source := ((fun gate => (field source gate, source.2.2 gate.1 gate.2)),
    source.1.1, table source)
  invFun source := ((source.2.1, fun adaptor bit => (source.1 (adaptor, bit)).1),
    (fun adaptor => Vector.ofFn fun bit => source.2.2 (adaptor, bit)),
    fun adaptor bit => (source.1 (adaptor, bit)).2)
  left_inv source := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext adaptor
        apply Vector.ext
        intro index valid
        simp only [Vector.getElem_ofFn]
        rfl
      · rfl
  right_inv source := by
    apply Prod.ext
    · funext gate
      rcases gate with ⟨adaptor, bit⟩
      rfl
    · apply Prod.ext
      · rfl
      · funext gate
        rcases gate with ⟨adaptor, bit⟩
        simp only [table, Vector.get_ofFn]

def goodSource (source : CurveMaskSample) : (Gate → FullHashLift) × HashRest :=
  ((fun gate => goodHashLiftSource ((hashSplit source).1 gate)), (hashSplit source).2)

/-- Complete fibers have exactly the prescribed actual false-field residues. -/
theorem goodSource_residues (source : CurveMaskSample) (gate : Gate) :
    field source gate = (((goodSource source).1 gate).val : BaseField) := by
  dsimp only [goodSource]
  rw [goodHashLiftSource_eq]
  exact (goodHashLift ((hashSplit source).1 gate).1 ((hashSplit source).1 gate).2).property.symm

/-- The whole1270-gate source rounding retains arbitrary observations of all
randomizers, ciphertexts, prefixes, and later adaptive continuations. -/
theorem hash_rounding_observation_bound {Observation : Type*}
    (observe : ((Gate → FullHashLift) × HashRest) → PMF Observation)
    (event : Set Observation) :
    |(((PMF.uniformOfFintype ((Gate → FullHashLift) × HashRest)).bind observe).toOuterMeasure event).toReal -
      (((PMF.uniformOfFintype CurveMaskSample).bind (observe ∘ goodSource)).toOuterMeasure event).toReal| ≤
        (1270 : ℝ) * (2 ^ 384 % baseFieldModulus : Nat) / 2 ^ 384 := by
  have transported : (PMF.uniformOfFintype CurveMaskSample).bind (observe ∘ goodSource) =
      (PMF.uniformOfFintype ((Gate → BaseField × HashLiftQuotient) × HashRest)).bind
        (fun pair => observe ((fun gate => goodHashLiftSource (pair.1 gate)), pair.2)) := by
    rw [← map_uniformOfFintype_equivBetween hashSplit, PMF.bind_map]
    rfl
  rw [transported]
  have bound := hashLift_family_product_observation_bound observe event
  have count : (Fintype.card Gate : ℝ) = 1270 := by exact_mod_cast gate_card
  rwa [count] at bound

/-- Complete words recover both original field and quotient. The rejected suffix
uses an explicit fallback; no quotient is silently discarded on the good source. -/
def readHash (word : FullHashLift) : BaseField × HashLiftQuotient :=
  match hashLiftSplitEquiv word with
  | .inl good => goodHashLiftEquiv good
  | .inr _ => ((word.val : BaseField), defaultHashLiftQuotient)

theorem readHash_good (pair : BaseField × HashLiftQuotient) :
    readHash (goodHashLiftSource pair) = pair := by
  unfold readHash goodHashLiftSource
  rw [hashLiftSplitEquiv.apply_symm_apply]
  exact goodHashLiftEquiv.apply_symm_apply pair

def decode (source : (Gate → FullHashLift) × HashRest) : CurveMaskSample :=
  hashSplit.symm ((fun gate => readHash (source.1 gate)), source.2)

theorem decode_good (source : CurveMaskSample) : decode (goodSource source) = source := by
  simp only [decode, goodSource, readHash_good]
  exact hashSplit.symm_apply_apply source

/-- The same bound applies to arbitrary observers of the COMPLETE mask sample,
including quotient-dependent continuations and every retained ciphertext row. -/
theorem retained_hash_rounding_observation_bound {Observation : Type*}
    (observe : CurveMaskSample → PMF Observation) (event : Set Observation) :
    |(((PMF.uniformOfFintype ((Gate → FullHashLift) × HashRest)).bind
        (observe ∘ decode)).toOuterMeasure event).toReal -
      (((PMF.uniformOfFintype CurveMaskSample).bind observe).toOuterMeasure event).toReal| ≤
        (1270 : ℝ) * (2 ^ 384 % baseFieldModulus : Nat) / 2 ^ 384 := by
  have bound := hash_rounding_observation_bound (observe ∘ decode) event
  simpa only [Function.comp_def, decode_good] using bound

set_option exponentiation.threshold 400 in
/-- This is only a conservative arithmetic bound on the retained-source rounding term. -/
theorem hash_rounding_le_blocks :
    (1270 : ℝ) * (2 ^ 384 % baseFieldModulus : Nat) / 2 ^ 384 ≤ 1270 / (2 : ℝ) ^ 128 := by
  norm_num [baseFieldModulus]

end
end Kriterion.ConditionalDisclosure.CurveSource
