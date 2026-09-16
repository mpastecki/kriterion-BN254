import Proof.ConditionalDisclosureHashSource
import Proof.ConditionalDisclosureAdaptiveSource

namespace Kriterion.ConditionalDisclosure.CurveSource

open BN254 Cryptography ArgoMAC ArgoMAC.Security
noncomputable section

/-- Every word is in the complete residue/quotient range. -/
def Complete (lifts : Gate → FullHashLift) : Prop :=
  ∀ gate, ∃ pair, goodHashLiftSource pair = lifts gate

def decodeTag (r1 r2 : BaseField) (tag : FullSource) : CurveMaskSample :=
  decode (tag.1, ![r1, r2], tag.2)

theorem decodeTag_randomizers (r1 r2 : BaseField) (tag : FullSource) :
    (decodeTag r1 r2 tag).1.1 = ![r1, r2] := rfl

theorem decodeTag_tables (r1 r2 : BaseField) (tag : FullSource) :
    table (decodeTag r1 r2 tag) = tag.2 := by
  funext gate
  rcases gate with ⟨adaptor, bit⟩
  simp only [decodeTag, decode, hashSplit, Equiv.symm, Equiv.coe_fn_mk, table, Vector.get_ofFn]

theorem decodeTag_residues (r1 r2 : BaseField) (tag : FullSource)
    (complete : Complete tag.1) (gate : Gate) :
    field (decodeTag r1 r2 tag) gate = ((tag.1 gate).val : BaseField) := by
  change (readHash (tag.1 gate)).1 = _
  obtain ⟨pair, equal⟩ := complete gate
  rw [← equal, readHash_good, goodHashLiftSource_eq]
  exact (goodHashLift pair.1 pair.2).property.symm

theorem decodeTag_lifts (r1 r2 : BaseField) (tag : FullSource)
    (complete : Complete tag.1) :
    (goodSource (decodeTag r1 r2 tag)).1 = tag.1 := by
  funext gate
  change goodHashLiftSource (readHash (tag.1 gate)) = tag.1 gate
  obtain ⟨pair, equal⟩ := complete gate
  rw [← equal, readHash_good]

/-- A complete actual source tag fixes the entire public curve table, including
its three field coefficients, for the fixed bridge and mask. -/
theorem actual_tag_table (bridge mask r1 r2 : BaseField) (tag : FullSource)
    (complete : Complete tag.1) (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (inputKey : InputMacKey) (same : actual bridge mask r1 r2 oracle inputKey = tag) :
    CurveMembership.garble bridge mask r1 r2 (Pipeline.curveOracles oracle) inputKey =
      sourceTable bridge mask (decodeTag r1 r2 tag) := by
  let source := decodeTag r1 r2 tag
  have hashes : ∀ gate, fixedDaviesMeyerHashLift (location gate) gate.2.val
      (key inputKey gate).falseLabel oracle = tag.1 gate :=
    fun gate => congrFun (congrArg Prod.fst same) gate
  have data : (maskSource bridge mask r1 r2 oracle inputKey source.2.2).1 = source.1 := by
    apply Prod.ext
    · rfl
    · funext adaptor bit
      have equal := fixedHashToField_of_lift oracle (location (adaptor, bit)) bit.val
        (key inputKey (adaptor, bit)).falseLabel (tag.1 (adaptor, bit)) (hashes (adaptor, bit))
      exact (actual_field bridge mask r1 r2 oracle inputKey source.2.2 (adaptor, bit)).trans
        (equal.trans (decodeTag_residues r1 r2 tag complete (adaptor, bit)).symm)
  have rows : table (maskSource bridge mask r1 r2 oracle inputKey source.2.2) = table source := by
    change (actual bridge mask r1 r2 oracle inputKey).2 = table (decodeTag r1 r2 tag)
    rw [same, decodeTag_tables]
  have sources : maskSource bridge mask r1 r2 oracle inputKey source.2.2 = source := by
    apply Prod.ext data
    apply Prod.ext
    · funext adaptor
      apply Vector.ext
      intro index valid
      exact congrFun rows (adaptor, ⟨index, valid⟩)
    · rfl
  rw [← sourceTable_actual bridge mask r1 r2 oracle inputKey source.2.2, sources]

end
end Kriterion.ConditionalDisclosure.CurveSource
