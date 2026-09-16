import Proof.DirectDisclosureSourceClosure

namespace Kriterion.ConditionalDisclosure.CurveSource

open BN254 Cryptography ArgoMAC ArgoMAC.Security
noncomputable section
attribute [local instance] rawBucketUseFintype fixedQueryDomainFintype residualFixedQueryDomainFintype
variable [Fintype Block] [Fintype Pipeline.FixedKeyIndex]

private theorem query_card_le (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (index : Pipeline.FixedKeyIndex) : Fintype.card (FixedQueryDomain history index) ≤ history.length :=
  (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ index)).trans
    (fixedQueryDomain_sum_card_le history)

private theorem small_capacity (queries : Nat) (small : queries < 2 ^ 100) :
    1 + queries ≤ Fintype.card Block := by
  have card : Fintype.card Block = 2 ^ 128 :=
    (Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin _)
  rw [card]
  norm_num at small ⊢
  omega

/-- One source assignment plus the complete prior query history fits every
physical permutation under the unchanged100-bit small-query split. -/
theorem prior_capacity (source : CurveMaskSample) (inputKey : InputMacKey)
    (lifts : Gate → FullHashLift) (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (queries : Nat) (small : queries < 2 ^ 100) (bounded : history.length ≤ queries)
    (index : Pipeline.FixedKeyIndex) :
    uses source inputKey lifts index + Fintype.card (FixedQueryDomain history index) ≤ Fintype.card Block := by
  have slot := bucket_card_le_one source inputKey lifts index
  have count := query_card_le history index
  have capacity := small_capacity queries small
  change Fintype.card (RawBucketUse (prescription source inputKey lifts) index) + _ ≤ _
  omega

/-- Removing covered domains can only decrease the postquery capacity count;
all legal repeated active queries remain allowed. -/
theorem residual_capacity (source : CurveMaskSample) (inputKey : InputMacKey)
    (lifts : Gate → FullHashLift) (history : List (PermutationRecord Pipeline.FixedKeyIndex Block))
    (covered : Pipeline.FixedKeyIndex → Set Block)
    (queries : Nat) (small : queries < 2 ^ 100) (bounded : history.length ≤ queries)
    (index : Pipeline.FixedKeyIndex) :
    uses source inputKey lifts index + Fintype.card (ResidualFixedQueryDomain history covered index) ≤
      Fintype.card Block := by
  have count := Fintype.card_le_of_injective
    (fun query : ResidualFixedQueryDomain history covered index => query.1) Subtype.val_injective
  have capacity := prior_capacity source inputKey lifts history queries small bounded index
  omega

end
end Kriterion.ConditionalDisclosure.CurveSource
