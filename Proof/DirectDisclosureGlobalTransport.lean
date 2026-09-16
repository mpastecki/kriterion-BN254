import Proof.DirectDisclosureSourceKernel
import Proof.DirectDisclosureFullSource
import Proof.DirectDisclosureSourceProduct

namespace Kriterion.DirectDisclosure.SourceKernel

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype bitAdaptorTableFintype
  publicVectorFintype ciphertextFintype curveMaskSampleFintype
local instance : Nonempty NonZeroBase := ⟨⟨1, by decide⟩⟩
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
local instance : Nonempty SimulatorOracleCoin := ⟨defaultSimulatorCoin.oracles⟩
local instance : Nonempty CurvePublicSample := ⟨defaultSimulatorCoin.tableSample.curve⟩
local instance : Nonempty CurveMaskSample :=
  ⟨((fun _ => 0, fun _ _ => 0), (fun _ => Vector.replicate coordinateBitCount defaultBitAdaptorTable),
    fun _ _ => defaultHashLiftQuotient)⟩
local instance : Nonempty Randomness.SourceProduct.TagSource :=
  ⟨(fun _ => 0, fun _ => 0, fun _ => defaultBitAdaptorTable)⟩

abbrev GlobalChoice (State : Type) := AffineInput × (SimulatorOracleCoin × InputMacKey ×
  (Public × State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer)))

def localChoice {State : Type} (choice : GlobalChoice State) : Choice State :=
  (choice.1, choice.2.2.2)

def chooseGlobal {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (table : Public) : PMF (GlobalChoice adversary.State) :=
  (PMF.uniformOfFintype SimulatorOracleCoin).bind fun oracles =>
    (PMF.uniformOfFintype InputMacKey).bind fun key =>
      (choose adversary parameter auxiliary table oracles).map fun choice =>
        (choice.1, oracles, key, choice.2)

def idealContinue [FieldCertificate] {Aux Observation : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (scalar : ScalarField) (auxiliary : Aux)
    (continuation : GlobalChoice adversary.State → CurveGateRequest → PMF Observation) : PMF Observation :=
  (PMF.uniformOfFintype CurvePublicSample).bind fun sample =>
    (chooseGlobal adversary parameter auxiliary sample.request.table).bind fun choice =>
      (PMF.uniformOfFintype BaseField).bind fun target =>
        continuation choice (sample.request.retarget choice.1 (MaskSource.selectedTarget (embedScalar scalar) choice.1 target))

def maskContinue {Aux Observation : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (scalar : ScalarField) (auxiliary : Aux)
    (continuation : GlobalChoice adversary.State → CurveGateRequest → PMF Observation) : PMF Observation :=
  (PMF.uniformOfFintype NonZeroBase).bind fun mask =>
    (PMF.uniformOfFintype CurveMaskSample).bind fun source =>
      (chooseGlobal adversary parameter auxiliary
        (ConditionalDisclosure.CurveSource.sourceTable (embedScalar scalar) mask.value source)).bind fun choice =>
          continuation choice (curveMaskSampleGarble (embedScalar scalar) mask.value choice.1 source).request

/-- One global fixed-bridge bound retains all independently sampled whole oracles,
the full key, complete prefix state, and an arbitrary randomized continuation. -/
theorem global_mask_bound [FieldCertificate] {Aux Observation : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (scalar : ScalarField) (auxiliary : Aux)
    (continuation : GlobalChoice adversary.State → CurveGateRequest → PMF Observation) (event : Set Observation) :
    |((idealContinue adversary parameter scalar auxiliary continuation).toOuterMeasure event).toReal -
      ((maskContinue adversary parameter scalar auxiliary continuation).toOuterMeasure event).toReal| ≤
        1 / (baseFieldModulus : ℝ) := by
  have bound := MaskSource.adaptive_nonzero_mask_observation_bound (embedScalar scalar)
    (chooseGlobal adversary parameter auxiliary)
    (fun choice mask _ source => continuation choice
      (curveMaskSampleGarble (embedScalar scalar) mask choice.1 source).request) event
  simpa only [MaskSource.reindexed_request, idealContinue, maskContinue] using bound

def fullContinue {Aux Observation : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (scalar : ScalarField) (auxiliary : Aux)
    (continuation : Bool → GlobalChoice adversary.State → CurveGateRequest → PMF Observation) : PMF Observation :=
  (PMF.uniformOfFintype NonZeroBase).bind fun mask =>
    (PMF.uniformOfFintype Randomness.SourceProduct.TagSource).bind fun full =>
      let source := ConditionalDisclosure.CurveSource.decode full
      (chooseGlobal adversary parameter auxiliary
        (ConditionalDisclosure.CurveSource.sourceTable (embedScalar scalar) mask.value source)).bind fun choice =>
          continuation (decide (¬ ConditionalDisclosure.CurveSource.Complete full.1)) choice
            (curveMaskSampleGarble (embedScalar scalar) mask.value choice.1 source).request

private theorem source_complete (source : CurveMaskSample) :
    ConditionalDisclosure.CurveSource.Complete (ConditionalDisclosure.CurveSource.goodSource source).1 :=
  fun gate => ⟨(ConditionalDisclosure.CurveSource.hashSplit source).1 gate, rfl⟩

/-- Full hash rounding transports the entire two-phase source, and explicitly marks
incomplete words. No rejected source word or retained private quotient is dropped. -/
theorem global_rounding_bound {Aux Observation : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (scalar : ScalarField) (auxiliary : Aux)
    (continuation : Bool → GlobalChoice adversary.State → CurveGateRequest → PMF Observation) (event : Set Observation) :
    |((fullContinue adversary parameter scalar auxiliary continuation).toOuterMeasure event).toReal -
      ((maskContinue adversary parameter scalar auxiliary (continuation false)).toOuterMeasure event).toReal| ≤
        (1270 : ℝ) * (2 ^ 384 % baseFieldModulus : Nat) / 2 ^ 384 := by
  let observe := fun full : Randomness.SourceProduct.TagSource =>
    (PMF.uniformOfFintype NonZeroBase).bind fun mask =>
      let source := ConditionalDisclosure.CurveSource.decode full
      (chooseGlobal adversary parameter auxiliary
        (ConditionalDisclosure.CurveSource.sourceTable (embedScalar scalar) mask.value source)).bind fun choice =>
          continuation (decide (¬ ConditionalDisclosure.CurveSource.Complete full.1)) choice
            (curveMaskSampleGarble (embedScalar scalar) mask.value choice.1 source).request
  have bound := ConditionalDisclosure.CurveSource.hash_rounding_observation_bound observe event
  dsimp only [observe, Function.comp_def] at bound
  simp only [source_complete, not_true_eq_false, decide_false,
    ConditionalDisclosure.CurveSource.decode_good] at bound
  unfold fullContinue maskContinue
  rw [PMF.bind_comm (PMF.uniformOfFintype NonZeroBase)
    (PMF.uniformOfFintype Randomness.SourceProduct.TagSource)]
  rw [PMF.bind_comm (PMF.uniformOfFintype NonZeroBase) (PMF.uniformOfFintype CurveMaskSample)]
  exact bound

end
end Kriterion.DirectDisclosure.SourceKernel
