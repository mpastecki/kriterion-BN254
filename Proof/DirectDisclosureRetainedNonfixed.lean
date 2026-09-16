import Proof.DirectDisclosureRetainedMass
import Proof.Privacy.Source.SourceTranscriptCompatibility

namespace Kriterion.DirectDisclosure.SourceKernel

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- Every retained good event satisfies every actual EncPRF/hash reply in both phases. -/
theorem retainedGoodEvent_nonfixed {Aux : Type}
    (scalar : ScalarField) (rest : GarblingSourceRest) (tag : FullTag) (publicTable : Public)
    (selected : AffineInput × Aux) (labels : Garbling.Labels)
    (before after : List (Sigma Garbling.oracleSpec.Answer)) (sample : OracleKey)
    (member : retainedGoodEvent scalar rest tag publicTable selected labels before after sample) :
    NonFixedTranscriptCompatible rest.reference (before ++ after) := by
  rcases member with ⟨_, _, _, _, _, priorProof, laterProof⟩
  apply (nonFixedTranscriptCompatible_append rest.reference before after).mpr
  constructor
  · exact idealTranscript_nonfixed (pairInitial rest sample.1) rest.reference before rfl rfl priorProof
  · apply idealTranscript_nonfixed _ rest.reference after _ _ laterProof
    · exact (programGateSchedule_encOracle _ _).trans
        ((idealTranscriptFinal_oracles (pairInitial rest sample.1) before).1.trans rfl)
    · exact (programGateSchedule_hashOracle _ _).trans
        ((idealTranscriptFinal_oracles (pairInitial rest sample.1) before).2.trans rfl)

/-- Incompatible nonfixed replies give exactly zero retained event mass. -/
theorem retainedGoodEvent_mass_zero [Fintype Block] {Aux : Type}
    (scalar : ScalarField) (rest : GarblingSourceRest) (tag : FullTag) (publicTable : Public)
    (selected : AffineInput × Aux) (labels : Garbling.Labels)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    (incompatible : ¬ NonFixedTranscriptCompatible rest.reference (before ++ after)) :
    (PMF.uniformOfFintype OracleKey).toOuterMeasure
      {sample | retainedGoodEvent scalar rest tag publicTable selected labels before after sample} = 0 := by
  have empty : {sample | retainedGoodEvent scalar rest tag publicTable selected labels before after sample} = ∅ := by
    ext sample
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun member => incompatible (retainedGoodEvent_nonfixed scalar rest tag publicTable selected labels before after sample member)
  rw [empty]
  simp

end
end Kriterion.DirectDisclosure.SourceKernel
