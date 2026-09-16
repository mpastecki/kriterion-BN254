import Proof.DirectDisclosureRetainedNonfixed
import Proof.DirectDisclosureSourceCapacity
import Proof.DirectDisclosureSourceDensity
import Proof.DirectDisclosureGoodProgramming

namespace Kriterion.DirectDisclosure.SourceKernel

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype bitAdaptorTableFintype
  transcriptOracleFintype fixedQueryDomainFintype residualFixedQueryDomainFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
local instance : Nonempty FullTag := ⟨(fun _ => 0, fun _ => defaultBitAdaptorTable)⟩

def retainedPrefix (reference : SimulatorState) (rest : GarblingSourceRest)
    (before : List (Sigma Garbling.oracleSpec.Answer)) : SimulatorState :=
  transcriptFinalState idealOracleHandler (sourcePrefixReference reference rest) before

private theorem mass_reorder (p v f m : ℝ≥0∞) : p * (v * f * m) = v * (p * f * m) := by ac_rfl

/-- Each complete good retained tag is dominated by the actual real tag event,
including its exact source and selected-label densities. All structural, reference,
and capacity premises of the raw counting theorem are discharged here. -/
theorem retained_good_tag_le
    (scalar : ScalarField) (rest : GarblingSourceRest) (tag : FullTag)
    (complete : ConditionalDisclosure.CurveSource.Complete tag.1)
    (input : AffineInput) (mac : InputMac) (reference : SimulatorState)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible idealOracleHandler reference before)
    (nonfixed : NonFixedTranscriptCompatible rest.reference (before ++ after))
    (good : ¬ LabelCollision.GridCollision (retainedPrefix reference rest before).fixedTranscript
      (LabelCollision.selectedUses (retainedRequest scalar rest tag input) input)
      (selectedPublicKey input (inputMacCoordinateEquiv mac)))
    (queries : Nat) (small : queries < 2 ^ 100) (bounded : (before ++ after).length ≤ queries) :
    (1 - (2 * (before ++ after).length : Nat) / (Fintype.card Block : ℝ≥0∞)) *
      ((PMF.uniformOfFintype FullTag) tag *
        (PMF.uniformOfFintype OracleKey).toOuterMeasure
          {sample | retainedJointEvent scalar rest tag input mac before after sample}) ≤
      ConditionalDisclosure.CurveSource.tagMass (embedScalar scalar) rest.algebraic.field.curveMask.value
        rest.algebraic.field.curveR1 rest.algebraic.field.curveR2 rest.reference input mac (before ++ after) tag := by
  let source := retainedSource rest tag
  let key := selectedPublicKey input (inputMacCoordinateEquiv mac)
  let state := retainedPrefix reference rest before
  let request := retainedRequest scalar rest tag input
  let schedule := request.schedule input mac
  have keyMac : key.encodeAffine input = mac :=
    (selectedPublicKey_encode input (inputMacCoordinateEquiv mac)).trans (inputMacCoordinateEquiv.symm_apply_apply mac)
  have nonfixedParts := (nonFixedTranscriptCompatible_append rest.reference before after).mp nonfixed
  have initialCompatible := sourcePrefixReference_compatible reference rest before compatible nonfixedParts.1
  letI : Nonempty (TranscriptOracle state.fixedTranscript) :=
    sourcePrefixReference_oracleExists reference rest before compatible
  have fresh : FreshRecordSchedule state.fixedTranscript (gateProgramRecords schedule) :=
    freshRecordSchedule_of_pairwise _ _
      (by simpa only [keyMac] using LabelCollision.selected_schedule_fresh request input key state.fixedTranscript good)
      (Simulation.selected_records_pairwise request input mac)
  have history : state.fixedTranscript = (fixedOracleTranscriptRecords before).reverse :=
    sourcePrefixReference_history reference rest before compatible
  have beforeLength : state.fixedTranscript.length ≤ queries := by
    rw [history, List.length_reverse]
    exact (fixedOracleTranscriptRecords_length_le before).trans
      ((Nat.le_add_right before.length after.length).trans (by simpa only [List.length_append] using bounded))
  have wholeLength : (state.fixedTranscript ++ fixedOracleTranscriptRecords after).length ≤ queries := by
    rw [List.length_append, history, List.length_reverse]
    exact (Nat.add_le_add (fixedOracleTranscriptRecords_length_le before)
      (fixedOracleTranscriptRecords_length_le after)).trans (by simpa only [List.length_append] using bounded)
  have schedules : ConditionalDisclosure.CurveSource.selectedSchedule (embedScalar scalar)
      rest.algebraic.field.curveMask.value source key input = schedule := by
    change request.schedule input (key.encodeAffine input) = _
    rw [keyMac]
  letI : Nonempty (TranscriptOracle
      (transcriptFinalState idealOracleHandler (pairInitial rest reference.fixedOracle) before).fixedTranscript) := by
    change Nonempty (TranscriptOracle state.fixedTranscript)
    infer_instance
  have normalized : (PMF.uniformOfFintype OracleKey).toOuterMeasure
      {sample | retainedJointEvent scalar rest tag input mac before after sample} =
      (Fintype.card (EncPRF.PermutationIndex → Block) : ℝ≥0∞)⁻¹ * fixedTranscriptFactor state.fixedTranscript *
        ((PMF.uniformOfFintype (TranscriptOracle state.fixedTranscript)).map fun oracle =>
          programGateSchedule {state with fixedOracle := oracle.1} schedule).toOuterMeasure
            {programmed | OracleTranscriptCompatible idealOracleHandler programmed after} := by
    have law := retained_joint_mass scalar rest tag input mac reference.fixedOracle before after initialCompatible
    have good' : ¬ LabelCollision.GridCollision
        (transcriptFinalState idealOracleHandler (pairInitial rest reference.fixedOracle) before).fixedTranscript
        (LabelCollision.selectedUses (retainedRequest scalar rest tag input) input)
        (selectedPublicKey input (inputMacCoordinateEquiv mac)) := good
    rw [if_pos good'] at law
    exact law
  have enc : state.encOracle = rest.encPRFOracle := (idealTranscriptFinal_oracles (sourcePrefixReference reference rest) before).1
  have hash : state.hashOracle = rest.hashOracle := (idealTranscriptFinal_oracles (sourcePrefixReference reference rest) before).2
  have afterMass := programGateSchedule_transcriptMass state schedule after fresh rest.reference enc hash
  rw [if_pos nonfixedParts.2] at afterMass
  have ratio := ConditionalDisclosure.CurveSource.selected_source_mass_le
    (embedScalar scalar) rest.algebraic.field.curveMask.value rest.algebraic.field.curveR1 rest.algebraic.field.curveR2
    source (ConditionalDisclosure.CurveSource.decodeTag_randomizers _ _ tag) key input state rest.reference before after
    nonfixed (sourcePrefixReference_members reference rest before compatible)
    (by simpa only [schedules] using fresh)
    (ConditionalDisclosure.CurveSource.prior_capacity source key
      (ConditionalDisclosure.CurveSource.selectedLifts source) state.fixedTranscript queries small beforeLength)
    (by
      rw [schedules]
      exact ConditionalDisclosure.CurveSource.residual_capacity source key
        (ConditionalDisclosure.CurveSource.selectedLifts source)
        (state.fixedTranscript ++ fixedOracleTranscriptRecords after) _ queries small wholeLength)
  rw [schedules, keyMac] at ratio
  have lifts : ConditionalDisclosure.CurveSource.selectedLifts source = tag.1 :=
    ConditionalDisclosure.CurveSource.decodeTag_lifts _ _ tag complete
  have rows : ConditionalDisclosure.CurveSource.table source = tag.2 :=
    ConditionalDisclosure.CurveSource.decodeTag_tables _ _ tag
  rw [lifts, rows] at ratio
  rw [normalized, afterMass, ConditionalDisclosure.CurveSource.fullSource_uniform_mass source key tag.1 tag, mass_reorder]
  exact ratio

end
end Kriterion.DirectDisclosure.SourceKernel
