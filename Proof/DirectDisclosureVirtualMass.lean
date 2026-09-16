import Proof.DirectDisclosureVirtualSource
import Proof.DirectDisclosureRealSourceSplit

namespace Kriterion.DirectDisclosure.SourceKernel

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable bitAdaptorTableFintype publicInputMacKeyFintype
local instance : Nonempty FullTag := ⟨(fun _ => 0, fun _ => defaultBitAdaptorTable)⟩
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

def virtualSamples (witness : Garbling.Randomness) (parameter : Nat) : PMF TapeSource :=
  (randomTape witness parameter).bind fun tape => (PMF.uniformOfFintype FullTag).map (Prod.mk tape)

def virtualGoodSource {Aux : Type} (witness : Garbling.Randomness) (parameter : Nat)
    (scalar : ScalarField) (publicTable : Public) (selected : AffineInput × Aux) (labels : Garbling.Labels)
    (before after : List (Sigma Garbling.oracleSpec.Answer)) : ℝ≥0∞ :=
  sampledTwoPhaseSourceMass idealOracleHandler (virtualSamples witness parameter)
    (fun source => tableOf scalar (Randomness.tapeSeed source.1) source.2)
    (fun source => initial (Randomness.tapeSeed source.1).oracles)
    (fun source state chosen => PMF.pure (sourceEncode scalar source state chosen.1))
    publicTable selected (labels, false) before after

/-- Good virtual transcript mass has the same two actual adversary weights as
the real transcript. The internal flag is never passed to either adversary program. -/
theorem fullFlagged_good_mass_factor {Aux : Type}
    (witness : Garbling.Randomness)
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (scalar : ScalarField) (auxiliary : Aux)
    (publicTable : Public) (selected : AffineInput × adversary.State) (labels : Garbling.Labels) (decision : Bool)
    (before after : List (Sigma Garbling.oracleSpec.Answer)) (referenceBefore referenceAfter : SimulatorState)
    (firstCompatible : OracleTranscriptCompatible idealOracleHandler referenceBefore before)
    (secondCompatible : OracleTranscriptCompatible idealOracleHandler referenceAfter after) :
    fullFlagged adversary parameter scalar auxiliary ((publicTable, selected, before, labels, decision, after), false) =
      ((runOracleProgramWithTranscript idealOracleHandler
        (adversary.chooseInput parameter publicTable auxiliary) referenceBefore).map
          (fun output => (output.1, output.2.2))) (selected, before) *
      ((runOracleProgramWithTranscript idealOracleHandler
        (adversary.decide parameter publicTable labels auxiliary selected.2) referenceAfter).map
          (fun output => (output.1, output.2.2))) (decision, after) *
      virtualGoodSource witness parameter scalar publicTable selected labels before after := by
  rw [fullFlagged_virtual]
  exact FlaggedMass.false_mass_factor idealOracleHandler idealOracleHandler _ _ _ _ _ _
    referenceBefore referenceAfter publicTable selected labels decision before after firstCompatible secondCompatible

def virtualGoodEvent {Aux : Type} (scalar : ScalarField) (publicTable : Public)
    (selected : AffineInput × Aux) (labels : Garbling.Labels)
    (before after : List (Sigma Garbling.oracleSpec.Answer)) (source : TapeSource) : Prop :=
  let seed := Randomness.tapeSeed source.1
  let state := initial seed.oracles
  let encoded := sourceEncode scalar source (transcriptFinalState idealOracleHandler state before) selected.1
  tableOf scalar seed source.2 = publicTable ∧ OracleTranscriptCompatible idealOracleHandler state before ∧
    encoded.1 = (labels, false) ∧ OracleTranscriptCompatible idealOracleHandler encoded.2 after

/-- This source event is exactly the deterministic encoding event of the virtual experiment. -/
theorem virtualGoodSource_event {Aux : Type} (witness : Garbling.Randomness) (parameter : Nat)
    (scalar : ScalarField) (publicTable : Public) (selected : AffineInput × Aux) (labels : Garbling.Labels)
    (before after : List (Sigma Garbling.oracleSpec.Answer)) :
    virtualGoodSource witness parameter scalar publicTable selected labels before after =
      (virtualSamples witness parameter).toOuterMeasure
        {source | virtualGoodEvent scalar publicTable selected labels before after source} := by
  unfold virtualGoodSource
  rw [sampledTwoPhaseSourceMass_pure]
  rfl

/-- Exact real-tape splitting and product reordering expose the complete tag and
actual fixed-oracle/key source used by the checked counting bound. -/
theorem virtualGoodSource_rest {Aux : Type} (witness : Garbling.Randomness) (parameter : Nat)
    (scalar : ScalarField) (publicTable : Public) (selected : AffineInput × Aux) (labels : Garbling.Labels)
    (before after : List (Sigma Garbling.oracleSpec.Answer)) :
    letI : Nonempty GarblingSourceRest := ⟨(garblingOracleKeyEquiv witness).2⟩
    virtualGoodSource witness parameter scalar publicTable selected labels before after =
      ∑' rest : GarblingSourceRest, (PMF.uniformOfFintype GarblingSourceRest) rest *
        ∑' tag : FullTag, (PMF.uniformOfFintype FullTag) tag *
          (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)).toOuterMeasure
            {sample | virtualGoodEvent scalar publicTable selected labels before after
              (garblingOracleKeyEquiv.symm (sample, rest), tag)} := by
  letI : Nonempty GarblingSourceRest := ⟨(garblingOracleKeyEquiv witness).2⟩
  have distribution : virtualSamples witness parameter =
      (PMF.uniformOfFintype GarblingSourceRest).bind fun rest =>
        (PMF.uniformOfFintype FullTag).bind fun tag =>
          (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey)).map
            (fun sample => (garblingOracleKeyEquiv.symm (sample, rest), tag)) := by
    unfold virtualSamples
    rw [randomTape_oracleKey, PMF.bind_bind]
    simp only [PMF.bind_map]
    apply congrArg ((PMF.uniformOfFintype GarblingSourceRest).bind)
    funext rest
    exact PMF.bind_comm
      (PMF.uniformOfFintype ((PermutationOracle Pipeline.FixedKeyIndex Block) × InputMacKey))
      (PMF.uniformOfFintype FullTag)
      (fun sample tag => PMF.pure (garblingOracleKeyEquiv.symm (sample, rest), tag))
  rw [virtualGoodSource_event, distribution, PMF.toOuterMeasure_bind_apply]
  simp only [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq]

end
end Kriterion.DirectDisclosure.SourceKernel
