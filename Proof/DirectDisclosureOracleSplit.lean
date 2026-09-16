import Proof.DirectDisclosureSimulator
import Proof.Privacy.Distribution.PublicDistribution

namespace Kriterion.DirectDisclosure.Simulation.OracleSplit

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] publicInputMacKeyFintype

abbrev FixedOracle := PermutationOracle Pipeline.FixedKeyIndex Block

/-- Everything in the actual simulator coin except its fixed permutation oracle.
The complete EncPRF and hash oracles are retained, including all unqueried entries. -/
structure Rest where
  curve : CurvePublicSample
  encOracle : PermutationOracle EncPRF.PermutationIndex Block
  hashOracle : EncPRF.HashOracle
  inputKey : InputMacKey
  target : BaseField
deriving Fintype

/-- Literal reconstruction of the entire actual coin. -/
def restore (rest : Rest) (fixedOracle : FixedOracle) : Coin := {
  curve := rest.curve
  oracles := ⟨fixedOracle, rest.encOracle, rest.hashOracle⟩
  inputKey := rest.inputKey
  target := rest.target }

/-- This equivalence projects away no randomness or transcript-relevant oracle data. -/
def coinEquiv : Coin ≃ FixedOracle × Rest where
  toFun coin := (coin.oracles.fixedOracle,
    ⟨coin.curve, coin.oracles.encOracle, coin.oracles.hashOracle, coin.inputKey, coin.target⟩)
  invFun value := restore value.2 value.1
  left_inv coin := by rcases coin with ⟨curve, ⟨fixed, enc, hash⟩, key, target⟩; rfl
  right_inv value := by rcases value with ⟨fixed, ⟨curve, enc, hash, key, target⟩⟩; rfl

instance restNonempty : Nonempty Rest :=
  ⟨(coinEquiv (Classical.choice (inferInstance : Nonempty Coin))).2⟩

/-- Exact uniform product decomposition of the simulator's original coin. -/
theorem uniform_coin :
    PMF.uniformOfFintype Coin =
      (PMF.uniformOfFintype Rest).bind fun rest =>
        (PMF.uniformOfFintype FixedOracle).map (restore rest) := by
  rw [← map_uniformOfFintype_equivBetween coinEquiv.symm, uniform_prod_eq_bind,
    PMF.map_bind]
  simp only [PMF.map_comp]
  rfl

/-- Arbitrary randomized observers retain access to the entire original coin. -/
theorem uniform_bind {Observation : Type*} (observe : Coin → PMF Observation) :
    (PMF.uniformOfFintype Coin).bind observe =
      (PMF.uniformOfFintype Rest).bind fun rest =>
        (PMF.uniformOfFintype FixedOracle).bind fun fixedOracle =>
          observe (restore rest fixedOracle) := by
  rw [uniform_coin, PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def]

/-- Every event of the full coin has its exact retained-rest/conditional-fixed mass. -/
theorem uniform_event (event : Coin → Prop) :
    (PMF.uniformOfFintype Coin).toOuterMeasure {coin | event coin} =
      ∑' rest : Rest, (Fintype.card Rest : ℝ≥0∞)⁻¹ *
        (PMF.uniformOfFintype FixedOracle).toOuterMeasure
          {fixedOracle | event (restore rest fixedOracle)} := by
  rw [uniform_coin, PMF.toOuterMeasure_bind_apply]
  simp only [PMF.uniformOfFintype_apply, PMF.toOuterMeasure_map_apply, Set.preimage_ofPred_eq]

/-- The same identity holds after any randomized observation of the whole coin. -/
theorem uniform_bind_event {Observation : Type*}
    (observe : Coin → PMF Observation) (event : Set Observation) :
    ((PMF.uniformOfFintype Coin).bind observe).toOuterMeasure event =
      ∑' rest : Rest, (Fintype.card Rest : ℝ≥0∞)⁻¹ *
        ((PMF.uniformOfFintype FixedOracle).bind fun fixedOracle =>
          observe (restore rest fixedOracle)).toOuterMeasure event := by
  rw [uniform_bind, PMF.toOuterMeasure_bind_apply]
  simp only [PMF.uniformOfFintype_apply]

end
end Kriterion.DirectDisclosure.Simulation.OracleSplit
