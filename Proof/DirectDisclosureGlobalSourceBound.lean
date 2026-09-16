import Proof.DirectDisclosureRetainedSum

namespace Kriterion.DirectDisclosure.SourceKernel

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable bitAdaptorTableFintype publicInputMacKeyFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
local instance : Nonempty FullTag := ⟨(fun _ => 0, fun _ => defaultBitAdaptorTable)⟩

/-- The exact good virtual source factor is below the ACTUAL real source factor,
after summing all original retained randomness and all complete raw tags. -/
theorem virtual_good_source_le {Aux : Type}
    (witness : Garbling.Randomness) (parameter : Nat) (scalar : NonZeroScalar) (publicTable : Public)
    (selected : AffineInput × Aux) (labels : Garbling.Labels) (reference : SimulatorState)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible idealOracleHandler reference before)
    (queries : Nat) (small : queries < 2 ^ 100) (bounded : (before ++ after).length ≤ queries) :
    (1 - (2 * (before ++ after).length : Nat) / (Fintype.card Block : ℝ≥0∞)) *
      virtualGoodSource witness parameter scalar.value publicTable selected labels before after ≤
      Endpoint.realSource witness parameter scalar publicTable selected.1 labels.inputMac before after := by
  letI : Nonempty GarblingSourceRest := ⟨(garblingOracleKeyEquiv witness).2⟩
  rw [virtualGoodSource_rest, Endpoint.realSource_split, ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro rest
  simp_rw [virtualGoodEvent_rest]
  rw [mul_left_comm]
  exact mul_le_mul' le_rfl
    (retained_source_sum_le scalar.value rest publicTable selected labels reference before after compatible queries small bounded)

/-- Incorrect canonical input bits have zero good source mass, independently of
all query or source conditions. -/
theorem virtualGoodSource_bits_zero {Aux : Type}
    (witness : Garbling.Randomness) (parameter : Nat) (scalar : ScalarField) (publicTable : Public)
    (selected : AffineInput × Aux) (labels : Garbling.Labels)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    (wrong : labels.input ≠ BitInput.ofAffine selected.1) :
    virtualGoodSource witness parameter scalar publicTable selected labels before after = 0 := by
  rw [virtualGoodSource_event]
  have empty : {source | virtualGoodEvent scalar publicTable selected labels before after source} = ∅ := by
    ext source
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro member
    have same := congrArg (fun pair : Garbling.Labels × Bool => pair.1.input) member.2.2.1
    have canonical : BitInput.ofAffine selected.1 = labels.input := same
    exact wrong canonical.symm
  rw [empty]
  simp

end
end Kriterion.DirectDisclosure.SourceKernel
