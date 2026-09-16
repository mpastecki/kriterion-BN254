import Proof.DirectDisclosureRandomness
import Proof.Privacy.Distribution.PublicSample
import Proof.Privacy.Distribution.PublicDistribution

namespace Kriterion.DirectDisclosure.Randomness

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] publicInputMacKeyFintype

/-- The actual direct garbler's complete used seed: a nonzero mask, both curve
randomizers, every fixed/EncPRF/hash oracle entry, and the full input MAC key. -/
structure Seed where
  mask : NonZeroBase
  r1 : BaseField
  r2 : BaseField
  oracles : SimulatorOracleCoin
  inputKey : InputMacKey
deriving Fintype

def seedOf (sample : CurveRandomness) : Seed := {
  mask := sample.1.curveMask
  r1 := sample.1.curveR1
  r2 := sample.1.curveR2
  oracles := ⟨sample.2.fixedKeyOracle, sample.2.encPRFOracle, sample.2.hashOracle⟩
  inputKey := sample.2.inputMacKey }

/-- The only extra field in the projected tape is its unused bridge key. -/
def seedEquiv : CurveRandomness ≃ Seed × BaseField where
  toFun sample := (seedOf sample, sample.1.bridgeKey)
  invFun sample := (⟨sample.2, sample.1.mask, sample.1.r1, sample.1.r2⟩,
    ⟨sample.1.oracles.fixedOracle, sample.1.inputKey,
      sample.1.oracles.encOracle, sample.1.oracles.hashOracle⟩)
  left_inv sample := by rcases sample with ⟨⟨bridge, mask, r1, r2⟩, ⟨fixed, key, enc, hash⟩⟩; rfl
  right_inv sample := by rcases sample with ⟨⟨mask, r1, r2, ⟨fixed, enc, hash⟩, key⟩, bridge⟩; rfl

def tapeSeed (tape : Garbling.Randomness) : Seed := seedOf (project tape)

/-- The product equivalence preserves arbitrary observers of every projected field. -/
theorem curve_uniform_bind (witness : CurveRandomness) {Observation : Type*}
    (observe : CurveRandomness → PMF Observation) :
    letI : Nonempty CurveRandomness := ⟨witness⟩
    letI : Nonempty Seed := ⟨seedOf witness⟩
    (PMF.uniformOfFintype CurveRandomness).bind observe =
      (PMF.uniformOfFintype Seed).bind fun seed =>
        (PMF.uniformOfFintype BaseField).bind fun bridge =>
          observe (seedEquiv.symm (seed, bridge)) := by
  let : Nonempty CurveRandomness := ⟨witness⟩
  let : Nonempty Seed := ⟨seedOf witness⟩
  rw [← map_uniformOfFintype_equivBetween seedEquiv.symm, PMF.bind_map,
    uniform_prod_eq_bind, PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def]
  exact PMF.bind_comm _ _ _

/-- Discarding only the independent unused bridge key gives an exact uniform seed. -/
theorem seedOf_uniform (witness : CurveRandomness) :
    letI : Nonempty CurveRandomness := ⟨witness⟩
    letI : Nonempty Seed := ⟨seedOf witness⟩
    (PMF.uniformOfFintype CurveRandomness).map seedOf = PMF.uniformOfFintype Seed := by
  let : Nonempty CurveRandomness := ⟨witness⟩
  let : Nonempty Seed := ⟨seedOf witness⟩
  have law := congrArg (fun distribution => distribution.map Prod.fst)
    (map_uniformOfFintype_equivBetween seedEquiv)
  rw [PMF.map_comp, map_uniform_prod_fst] at law
  exact law

/-- The unchanged actual real random tape has exactly this full used-seed marginal.
The pre-existing projection accounts for its universally clamped unused point data. -/
theorem tapeSeed_uniform (witness : Garbling.Randomness) (parameter : Nat) :
    letI : Nonempty Seed := ⟨tapeSeed witness⟩
    (randomTape witness parameter).map tapeSeed = PMF.uniformOfFintype Seed := by
  let : Nonempty CurveRandomness := ⟨project witness⟩
  let : Nonempty Seed := ⟨tapeSeed witness⟩
  change (randomTape witness parameter).map (seedOf ∘ project) = _
  rw [← PMF.map_comp, project_uniform, seedOf_uniform (project witness)]

/-- Arbitrary randomized observers of the complete used seed have the exact same law. -/
theorem tapeSeed_bind (witness : Garbling.Randomness) (parameter : Nat)
    {Observation : Type*} (observe : Seed → PMF Observation) :
    letI : Nonempty Seed := ⟨tapeSeed witness⟩
    (randomTape witness parameter).bind (fun tape => observe (tapeSeed tape)) =
      (PMF.uniformOfFintype Seed).bind observe := by
  let : Nonempty Seed := ⟨tapeSeed witness⟩
  have law := congrArg (fun distribution => distribution.bind observe) (tapeSeed_uniform witness parameter)
  simpa only [PMF.bind_map, Function.comp_def] using law

/-- The marginal identity preserves events involving all retained oracle functions. -/
theorem tapeSeed_event (witness : Garbling.Randomness) (parameter : Nat) (event : Seed → Prop) :
    letI : Nonempty Seed := ⟨tapeSeed witness⟩
    (randomTape witness parameter).toOuterMeasure {tape | event (tapeSeed tape)} =
      (PMF.uniformOfFintype Seed).toOuterMeasure {seed | event seed} := by
  let : Nonempty Seed := ⟨tapeSeed witness⟩
  rw [← tapeSeed_uniform witness parameter, PMF.toOuterMeasure_map_apply]
  rfl

end
end Kriterion.DirectDisclosure.Randomness
