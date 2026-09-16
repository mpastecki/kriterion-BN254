import Proof.ConditionalDisclosureProgramRatio

namespace Kriterion.ConditionalDisclosure.CurveSource

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] bitAdaptorTableFintype rawBucketUseFintype
local instance : Nonempty FullSource := ⟨(fun _ => 0, fun _ => defaultBitAdaptorTable)⟩

/-- The raw fibers partition all five permutation slots of all1270 curve gates. -/
theorem uses_sum (source : CurveMaskSample) (inputKey : InputMacKey) (lifts : Gate → FullHashLift) :
    ∑ index, uses source inputKey lifts index = 6350 := by
  let gates := prescription source inputKey lifts
  have counted := Fintype.card_congr (Equiv.sigmaFiberEquiv
    (fun use : Gate × Pipeline.FixedKeySlot =>
      fixedKeyIndex (gates use.1).location (gates use.1).window use.2))
  change Fintype.card ((index : Pipeline.FixedKeyIndex) × RawBucketUse gates index) = _ at counted
  rw [Fintype.card_sigma, Fintype.card_prod, gate_card] at counted
  have slots : Fintype.card Pipeline.FixedKeySlot = 5 := by decide
  rw [slots] at counted
  exact counted

/-- The full-word/row source density is exactly the factor in the actual
permutation count. No source entropy is silently discarded. -/
theorem fullSource_uniform_mass [Fintype Block]
    (source : CurveMaskSample) (inputKey : InputMacKey) (lifts : Gate → FullHashLift)
    (tag : FullSource) :
    (PMF.uniformOfFintype FullSource) tag = sourceFactor source inputKey lifts := by
  rw [PMF.uniformOfFintype_apply, fullSource_card, Nat.cast_pow]
  rw [← uses_sum source inputKey lifts, ← Finset.prod_pow_eq_pow_sum]
  unfold sourceFactor
  apply ENNReal.prod_inv_distrib
  intro _ _ _ _ _
  exact Or.inr (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))

end
end Kriterion.ConditionalDisclosure.CurveSource
