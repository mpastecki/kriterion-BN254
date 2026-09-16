import Proof.DirectDisclosureGlobalTransport
import Proof.DirectDisclosureCoinProduct
import Proof.DirectDisclosurePrefixCollision

namespace Kriterion.DirectDisclosure.SourceKernel

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
local instance : Nonempty SimulatorOracleCoin := ⟨defaultSimulatorCoin.oracles⟩
local instance : Nonempty CurvePublicSample := ⟨defaultSimulatorCoin.tableSample.curve⟩

/-- The flag records either an incomplete source word or the exact selected
program/prefix label collision. The full observed transcript is retained. -/
def flagObserve {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (incomplete : Bool)
    (choice : GlobalChoice adversary.State) (request : CurveGateRequest) :
    PMF (Transcript adversary.State × Bool) :=
  (observe adversary parameter auxiliary choice.2.2.1 (localChoice choice) request).map fun output =>
    (output, incomplete || decide (LabelCollision.GridCollision
      (localChoice choice).2.2.2.1.fixedTranscript (LabelCollision.selectedUses request choice.1) choice.2.2.1))

def idealFlagged [FieldCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (scalar : ScalarField) (auxiliary : Aux) : PMF (Transcript adversary.State × Bool) :=
  idealContinue adversary parameter scalar auxiliary (flagObserve adversary parameter auxiliary false)

def fullFlagged {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (scalar : ScalarField) (auxiliary : Aux) : PMF (Transcript adversary.State × Bool) :=
  fullContinue adversary parameter scalar auxiliary (flagObserve adversary parameter auxiliary)

/-- The global choice kernel has exactly the original whole-coin ideal law. -/
theorem global_ideal_observe [FieldCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (scalar : ScalarField) (auxiliary : Aux) :
    idealContinue adversary parameter scalar auxiliary
      (fun choice request => observe adversary parameter auxiliary choice.2.2.1 (localChoice choice) request) =
      (PMF.uniformOfFintype Simulation.Coin).bind (ideal adversary parameter scalar auxiliary) := by
  rw [Simulation.CoinProduct.coin_uniform_bind]
  unfold idealContinue chooseGlobal ideal run
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def, localChoice]
  apply congrArg ((PMF.uniformOfFintype CurvePublicSample).bind)
  funext sample
  rw [PMF.bind_comm (PMF.uniformOfFintype BaseField) (PMF.uniformOfFintype SimulatorOracleCoin)]
  apply congrArg ((PMF.uniformOfFintype SimulatorOracleCoin).bind)
  funext oracles
  rw [PMF.bind_comm (PMF.uniformOfFintype BaseField) (PMF.uniformOfFintype InputMacKey)]
  apply congrArg ((PMF.uniformOfFintype InputMacKey).bind)
  funext key
  exact (PMF.bind_comm (PMF.uniformOfFintype BaseField)
    (choose adversary parameter auxiliary sample.request.table oracles)
    (fun target choice => observe adversary parameter auxiliary key choice
      (sample.request.retarget choice.1 (MaskSource.selectedTarget (embedScalar scalar) choice.1 target)))).symm

/-- Erasing only the source flag yields the ACTUAL ideal transcript distribution. -/
theorem idealFlagged_projection [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :
    (idealFlagged adversary parameter scalar.value auxiliary).map Prod.fst =
      idealAdaptiveTranscriptWithState internalScheme topology Simulation.simulator Simulation.handler
        adversary parameter scalar auxiliary := by
  rw [actual_ideal_transcript, ← global_ideal_observe]
  simp only [idealFlagged, idealContinue, flagObserve, PMF.map_bind, PMF.map_comp,
    Function.comp_def]
  have identity (p : PMF (Transcript adversary.State)) : PMF.map (fun x => x) p = p := PMF.map_id p
  simp only [identity]

/-- Joint flag-and-transcript distance retains the exact bad event needed by the
source lower bound, instead of transferring only a transcript marginal. -/
theorem flagged_transport_bound [FieldCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (scalar : ScalarField) (auxiliary : Aux)
    (event : Set (Transcript adversary.State × Bool)) :
    |((idealFlagged adversary parameter scalar auxiliary).toOuterMeasure event).toReal -
      ((fullFlagged adversary parameter scalar auxiliary).toOuterMeasure event).toReal| ≤
        1 / (baseFieldModulus : ℝ) + (1270 : ℝ) * (2 ^ 384 % baseFieldModulus : Nat) / 2 ^ 384 := by
  have mask := global_mask_bound adversary parameter scalar auxiliary
    (flagObserve adversary parameter auxiliary false) event
  have rounding := global_rounding_bound adversary parameter scalar auxiliary
    (flagObserve adversary parameter auxiliary) event
  rw [abs_sub_comm] at rounding
  exact (abs_sub_le _ _ _).trans (add_le_add mask rounding)

end
end Kriterion.DirectDisclosure.SourceKernel
