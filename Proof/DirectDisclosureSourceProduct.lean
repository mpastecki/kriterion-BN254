import Proof.DirectDisclosureSeed
import Proof.ConditionalDisclosureHashSource

namespace Kriterion.DirectDisclosure.Randomness.SourceProduct

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open ConditionalDisclosure.CurveSource
open scoped ENNReal
noncomputable section
attribute [local instance] publicInputMacKeyFintype bitAdaptorTableFintype

/-- The nonrandomizer part of the real seed, retaining all three whole oracles. -/
structure Ambient where
  mask : NonZeroBase
  oracles : SimulatorOracleCoin
  inputKey : InputMacKey
deriving Fintype

abbrev TagSource := (Gate → FullHashLift) × HashRest

/-- Reassociate every source coordinate; the two randomizers become one Fin2 function. -/
def sourceEquiv : Seed × FullSource ≃ Ambient × TagSource where
  toFun sample := (⟨sample.1.mask, sample.1.oracles, sample.1.inputKey⟩,
    sample.2.1, ![sample.1.r1, sample.1.r2], sample.2.2)
  invFun sample := (⟨sample.1.mask, sample.2.2.1 0, sample.2.2.1 1,
    sample.1.oracles, sample.1.inputKey⟩, sample.2.1, sample.2.2.2)
  left_inv sample := by rcases sample with ⟨⟨mask, r1, r2, oracles, key⟩, lifts, rows⟩; rfl
  right_inv sample := by
    rcases sample with ⟨⟨mask, oracles, key⟩, lifts, randomizers, rows⟩
    have randomizers_eq : ![randomizers 0, randomizers 1] = randomizers := by
      funext i
      fin_cases i <;> rfl
    change ((⟨mask, oracles, key⟩ : Ambient), lifts, ![randomizers 0, randomizers 1], rows) = _
    rw [randomizers_eq]

local instance : Nonempty Seed :=
  ⟨⟨⟨1, by decide⟩, 0, 0, defaultSimulatorCoin.oracles, defaultSimulatorCoin.inputKey⟩⟩
local instance : Nonempty Ambient :=
  ⟨⟨⟨1, by decide⟩, defaultSimulatorCoin.oracles, defaultSimulatorCoin.inputKey⟩⟩
local instance : Nonempty FullSource := ⟨(fun _ => 0, fun _ => defaultBitAdaptorTable)⟩
local instance : Nonempty TagSource :=
  ⟨(fun _ => 0, fun _ => 0, fun _ => defaultBitAdaptorTable)⟩

/-- Exact uniform law of the literal whole-source equivalence. -/
theorem uniform_product :
    (PMF.uniformOfFintype (Seed × FullSource)).map sourceEquiv =
      PMF.uniformOfFintype (Ambient × TagSource) :=
  map_uniformOfFintype_equivBetween sourceEquiv

/-- Arbitrary whole-pair observers see the same distribution after reassociation. -/
theorem uniform_bind {Observation : Type*} (observe : Seed × FullSource → PMF Observation) :
    (PMF.uniformOfFintype (Seed × FullSource)).bind observe =
      (PMF.uniformOfFintype Ambient).bind fun ambient =>
        (PMF.uniformOfFintype TagSource).bind fun tag =>
          observe (sourceEquiv.symm (ambient, tag)) := by
  rw [← map_uniformOfFintype_equivBetween sourceEquiv.symm, PMF.bind_map,
    uniform_prod_eq_bind, PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def]
  exact PMF.bind_comm _ _ _

/-- Separate real-seed and full-source draws have the same exact retained observation law. -/
theorem independent_bind {Observation : Type*} (observe : Seed → FullSource → PMF Observation) :
    ((PMF.uniformOfFintype Seed).bind fun seed =>
      (PMF.uniformOfFintype FullSource).bind (observe seed)) =
      (PMF.uniformOfFintype Ambient).bind fun ambient =>
        (PMF.uniformOfFintype TagSource).bind fun tag =>
          observe (sourceEquiv.symm (ambient, tag)).1 (sourceEquiv.symm (ambient, tag)).2 := by
  rw [← uniform_bind (fun sample => observe sample.1 sample.2),
    uniform_prod_eq_bind (First := Seed) (Second := FullSource), PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def]
  exact PMF.bind_comm _ _ _

/-- Exact event law, retaining every row, full lift, key, and oracle function. -/
theorem uniform_event (event : Seed × FullSource → Prop) :
    (PMF.uniformOfFintype (Seed × FullSource)).toOuterMeasure {sample | event sample} =
      ∑' ambient : Ambient, (Fintype.card Ambient : ℝ≥0∞)⁻¹ *
        (PMF.uniformOfFintype TagSource).toOuterMeasure
          {tag | event (sourceEquiv.symm (ambient, tag))} := by
  have law : PMF.uniformOfFintype (Seed × FullSource) =
      (PMF.uniformOfFintype Ambient).bind fun ambient =>
        (PMF.uniformOfFintype TagSource).map (fun tag => sourceEquiv.symm (ambient, tag)) := by
    simpa only [PMF.bind_pure, PMF.map, Function.comp_def] using uniform_bind (fun sample => PMF.pure sample)
  rw [law, PMF.toOuterMeasure_bind_apply]
  simp only [PMF.uniformOfFintype_apply, PMF.toOuterMeasure_map_apply, Set.preimage_ofPred_eq]

/-- Events after randomized whole-source observations obey the same retained law. -/
theorem uniform_bind_event {Observation : Type*}
    (observe : Seed × FullSource → PMF Observation) (event : Set Observation) :
    ((PMF.uniformOfFintype (Seed × FullSource)).bind observe).toOuterMeasure event =
      ∑' ambient : Ambient, (Fintype.card Ambient : ℝ≥0∞)⁻¹ *
        ((PMF.uniformOfFintype TagSource).bind fun tag =>
          observe (sourceEquiv.symm (ambient, tag))).toOuterMeasure event := by
  rw [uniform_bind, PMF.toOuterMeasure_bind_apply]
  simp only [PMF.uniformOfFintype_apply]

end
end Kriterion.DirectDisclosure.Randomness.SourceProduct
