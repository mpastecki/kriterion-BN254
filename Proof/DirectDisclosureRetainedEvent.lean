import Proof.DirectDisclosureVirtualMass
import Proof.DirectDisclosurePrefixKeyMass
import Proof.Privacy.Source.SourcePrefixReference

namespace Kriterion.DirectDisclosure.SourceKernel

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype bitAdaptorTableFintype

abbrev OracleKey := PermutationOracle Pipeline.FixedKeyIndex Block × InputMacKey

def retainedSeed (rest : GarblingSourceRest) (sample : OracleKey) : Randomness.Seed := {
  mask := rest.algebraic.field.curveMask
  r1 := rest.algebraic.field.curveR1
  r2 := rest.algebraic.field.curveR2
  oracles := ⟨sample.1, rest.encPRFOracle, rest.hashOracle⟩
  inputKey := sample.2 }

theorem seed_restored (rest : GarblingSourceRest) (sample : OracleKey) :
    Randomness.tapeSeed (garblingOracleKeyEquiv.symm (sample, rest)) = retainedSeed rest sample := rfl

def retainedSource (rest : GarblingSourceRest) (tag : FullTag) : CurveMaskSample :=
  ConditionalDisclosure.CurveSource.decodeTag rest.algebraic.field.curveR1 rest.algebraic.field.curveR2 tag

def retainedTable (scalar : ScalarField) (rest : GarblingSourceRest) (tag : FullTag) : Public :=
  ConditionalDisclosure.CurveSource.sourceTable (embedScalar scalar) rest.algebraic.field.curveMask.value
    (retainedSource rest tag)

def retainedRequest (scalar : ScalarField) (rest : GarblingSourceRest) (tag : FullTag) (input : AffineInput) : CurveGateRequest :=
  (curveMaskSampleGarble (embedScalar scalar) rest.algebraic.field.curveMask.value input (retainedSource rest tag)).request

def pairInitial (rest : GarblingSourceRest) (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) : SimulatorState :=
  initial ⟨oracle, rest.encPRFOracle, rest.hashOracle⟩

/-- This event displays the exact static source guards separately from the joint
fixed-oracle/key event normalized by the prefix-key theorem. -/
def retainedGoodEvent {Aux : Type} (scalar : ScalarField) (rest : GarblingSourceRest) (tag : FullTag)
    (publicTable : Public) (selected : AffineInput × Aux) (labels : Garbling.Labels)
    (before after : List (Sigma Garbling.oracleSpec.Answer)) (sample : OracleKey) : Prop :=
  ConditionalDisclosure.CurveSource.Complete tag.1 ∧ retainedTable scalar rest tag = publicTable ∧
    BitInput.ofAffine selected.1 = labels.input ∧
    sample.2.encodeAffine selected.1 = labels.inputMac ∧
    ¬ LabelCollision.GridCollision
      (transcriptFinalState idealOracleHandler (pairInitial rest sample.1) before).fixedTranscript
      (LabelCollision.selectedUses (retainedRequest scalar rest tag selected.1) selected.1) sample.2 ∧
    OracleTranscriptCompatible idealOracleHandler (pairInitial rest sample.1) before ∧
    OracleTranscriptCompatible idealOracleHandler
      (programGateSchedule (transcriptFinalState idealOracleHandler (pairInitial rest sample.1) before)
        ((retainedRequest scalar rest tag selected.1).schedule selected.1 (sample.2.encodeAffine selected.1))) after

/-- No approximation is involved: the actual virtual source event is the displayed
complete-source/selected-label/whole-transcript event after literal tape reconstruction. -/
theorem virtualGoodEvent_rest {Aux : Type} (scalar : ScalarField) (rest : GarblingSourceRest) (tag : FullTag)
    (publicTable : Public) (selected : AffineInput × Aux) (labels : Garbling.Labels)
    (before after : List (Sigma Garbling.oracleSpec.Answer)) (sample : OracleKey) :
    virtualGoodEvent scalar publicTable selected labels before after
      (garblingOracleKeyEquiv.symm (sample, rest), tag) ↔
      retainedGoodEvent scalar rest tag publicTable selected labels before after sample := by
  unfold virtualGoodEvent sourceEncode
  simp only [seed_restored]
  rcases labels with ⟨bits, mac⟩
  simp only [Prod.mk.injEq, Garbling.Labels.mk.injEq, Bool.or_eq_false_iff,
    decide_eq_false_iff_not, not_not]
  change (_ ∧ _ ∧ ((_ ∧ _) ∧ (_ ∧ _)) ∧ _) ↔ _
  unfold retainedGoodEvent
  dsimp only [retainedSeed, tableOf, requestOf, sourceOf, retainedTable, retainedRequest,
    retainedSource, pairInitial]
  constructor
  · rintro ⟨tableEqual, priorProof, ⟨⟨bitsEqual, macEqual⟩, ⟨complete, grid⟩⟩, laterProof⟩
    exact ⟨complete, tableEqual, bitsEqual, macEqual, of_decide_eq_false grid, priorProof, laterProof⟩
  · rintro ⟨complete, tableEqual, bitsEqual, macEqual, grid, priorProof, laterProof⟩
    exact ⟨tableEqual, priorProof, ⟨⟨bitsEqual, macEqual⟩, ⟨complete, decide_eq_false_iff_not.mpr grid⟩⟩, laterProof⟩

end
end Kriterion.DirectDisclosure.SourceKernel
