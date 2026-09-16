import Proof.DirectDisclosureEndpointMass
import Proof.DirectDisclosureSourceSum
import Proof.Privacy.Source.RealSourceSum

namespace Kriterion.DirectDisclosure.Endpoint

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- The retained source fixes both untouched oracles and every unused algebraic
field, while the actual fixed-permutation oracle and actual label key are sampled. -/
def retainedPublicMass [Fintype Block] (scalar : ScalarField) (rest : GarblingSourceRest)
    (publicTable : Public) (input : AffineInput) (mac : InputMac)
    (transcript : List (Sigma Garbling.oracleSpec.Answer)) : ℝ≥0∞ :=
  ConditionalDisclosure.CurveSource.publicMass (embedScalar scalar) rest.algebraic.field.curveMask.value
    rest.algebraic.field.curveR1 rest.algebraic.field.curveR2 rest.reference input mac transcript publicTable

/-- This is the actual source factor from the two-phase real endpoint, split by
an exact random-tape product equivalence. Every prior and later oracle reply remains. -/
theorem realSource_split [Fintype Block] (witness : Garbling.Randomness) (parameter : Nat)
    (scalar : NonZeroScalar) (publicTable : Public) (input : AffineInput) (mac : InputMac)
    (before after : List (Sigma Garbling.oracleSpec.Answer)) :
    letI : Nonempty GarblingSourceRest := ⟨(garblingOracleKeyEquiv witness).2⟩
    realSource witness parameter scalar publicTable input mac before after =
      ∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
        retainedPublicMass scalar.value rest publicTable input mac (before ++ after) := by
  letI : Nonempty GarblingSourceRest := ⟨(garblingOracleKeyEquiv witness).2⟩
  unfold realSource
  rw [randomTape_oracleKey, PMF.toOuterMeasure_bind_apply]
  simp only [PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq]
  apply tsum_congr
  intro rest
  apply congrArg ((PMF.uniformOfFintype GarblingSourceRest) rest * ·)
  unfold retainedPublicMass ConditionalDisclosure.CurveSource.publicMass
  congr 1
  ext sample
  simp only [Set.mem_setOf_eq, sourceRest_transcriptCompatible]
  rfl

end
end Kriterion.DirectDisclosure.Endpoint
