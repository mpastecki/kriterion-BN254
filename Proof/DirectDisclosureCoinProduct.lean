import Proof.DirectDisclosureSimulator
import Proof.DirectDisclosureSourceProduct

namespace Kriterion.DirectDisclosure.Simulation.CoinProduct

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open Randomness.SourceProduct
noncomputable section
attribute [local instance] publicInputMacKeyFintype

local instance : Nonempty CurvePublicSample :=
  ⟨(Classical.choice (inferInstance : Nonempty Coin)).curve⟩
local instance : Nonempty SimulatorOracleCoin := ⟨defaultSimulatorCoin.oracles⟩
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
local instance : Nonempty NonZeroBase := ⟨⟨1, by decide⟩⟩
local instance : Nonempty Ambient :=
  ⟨⟨⟨1, by decide⟩, defaultSimulatorCoin.oracles, defaultSimulatorCoin.inputKey⟩⟩

/-- Reassociate the complete simulator coin into independent finite coordinates. -/
def coinEquiv : Coin ≃ InputMacKey × (SimulatorOracleCoin × (BaseField × CurvePublicSample)) where
  toFun coin := (coin.inputKey, coin.oracles, coin.target, coin.curve)
  invFun sample := ⟨sample.2.2.2, sample.2.1, sample.1, sample.2.2.1⟩
  left_inv coin := by cases coin; rfl
  right_inv sample := rfl

/-- Exact sampling order of the actual whole coin: curve, target, all oracles, key. -/
theorem coin_uniform_bind {Observation : Type*} (observe : Coin → PMF Observation) :
    (PMF.uniformOfFintype Coin).bind observe =
      (PMF.uniformOfFintype CurvePublicSample).bind fun curve =>
        (PMF.uniformOfFintype BaseField).bind fun target =>
          (PMF.uniformOfFintype SimulatorOracleCoin).bind fun oracles =>
            (PMF.uniformOfFintype InputMacKey).bind fun inputKey =>
              observe ⟨curve, oracles, inputKey, target⟩ := by
  rw [← map_uniformOfFintype_equivBetween coinEquiv.symm, PMF.bind_map]
  simp_rw [uniform_prod_eq_bind, PMF.bind_bind, PMF.bind_map]
  rfl

/-- The full ambient source has exactly mask/oracle/key coordinates. -/
def ambientEquiv : Ambient ≃ InputMacKey × (SimulatorOracleCoin × NonZeroBase) where
  toFun ambient := (ambient.inputKey, ambient.oracles, ambient.mask)
  invFun sample := ⟨sample.2.2, sample.2.1, sample.1⟩
  left_inv ambient := by cases ambient; rfl
  right_inv sample := rfl

/-- Exact ambient order, with every fixed/EncPRF/hash oracle entry retained. -/
theorem ambient_uniform_bind {Observation : Type*} (observe : Ambient → PMF Observation) :
    (PMF.uniformOfFintype Ambient).bind observe =
      (PMF.uniformOfFintype NonZeroBase).bind fun mask =>
        (PMF.uniformOfFintype SimulatorOracleCoin).bind fun oracles =>
          (PMF.uniformOfFintype InputMacKey).bind fun inputKey =>
            observe ⟨mask, oracles, inputKey⟩ := by
  rw [← map_uniformOfFintype_equivBetween ambientEquiv.symm, PMF.bind_map]
  simp_rw [uniform_prod_eq_bind, PMF.bind_bind, PMF.bind_map]
  rfl

end
end Kriterion.DirectDisclosure.Simulation.CoinProduct
