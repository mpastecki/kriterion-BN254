import Proof.DirectDisclosureFlaggedKernel

namespace Kriterion.DirectDisclosure.SourceKernel

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable publicInputMacKeyFintype
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
local instance : Nonempty SimulatorOracleCoin := ⟨defaultSimulatorCoin.oracles⟩
local instance : Nonempty CurvePublicSample := ⟨defaultSimulatorCoin.tableSample.curve⟩

private theorem map_constant {A B : Type*} (p : PMF A) (value : B) :
    p.map (fun _ => value) = PMF.pure value := PMF.map_const p value

private def coinGridFlag [FieldCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (scalar : ScalarField) (auxiliary : Aux) (coin : Simulation.Coin) : PMF Bool :=
  (choose adversary parameter auxiliary coin.curve.request.table coin.oracles).map fun choice =>
    decide (LabelCollision.GridCollision choice.2.2.2.1.fixedTranscript
      (LabelCollision.selectedUses (coin.curve.request.retarget choice.1
        (MaskSource.selectedTarget (embedScalar scalar) choice.1 coin.target)) choice.1) coin.inputKey)

private theorem idealFlagged_snd_coin [FieldCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (scalar : ScalarField) (auxiliary : Aux) :
    (idealFlagged adversary parameter scalar auxiliary).map Prod.snd =
      (PMF.uniformOfFintype Simulation.Coin).bind (coinGridFlag adversary parameter scalar auxiliary) := by
  rw [Simulation.CoinProduct.coin_uniform_bind]
  unfold idealFlagged idealContinue chooseGlobal flagObserve coinGridFlag
  simp only [PMF.map_bind, PMF.bind_bind, PMF.bind_map, PMF.map_comp,
    Function.comp_def, localChoice, Bool.false_or, map_constant]
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
    (fun target choice => PMF.pure (decide (LabelCollision.GridCollision
      choice.2.2.2.1.fixedTranscript (LabelCollision.selectedUses
        (sample.request.retarget choice.1 (MaskSource.selectedTarget (embedScalar scalar) choice.1 target))
        choice.1) key)))).symm

private theorem coinGridFlag_prefix [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (scalar : ScalarField) (auxiliary : Aux) (coin : Simulation.Coin) :
    coinGridFlag adversary parameter scalar auxiliary coin =
      ((adversary.chooseInput parameter coin.state.table auxiliary).run Simulation.handler coin.state).map
        (fun chosen => decide (Simulation.Prefix.gridBad chosen.2 chosen.1.1
          (checkedScalarMultiplication scalar chosen.1.1))) := by
  rw [← runOracleProgramWithTranscript_erase Simulation.handler
    (adversary.chooseInput parameter coin.state.table auxiliary) coin.state,
    transcript_lift, PMF.map_comp, PMF.map_comp]
  unfold coinGridFlag choose
  simp only [PMF.map_comp, Function.comp_def, Simulation.Prefix.gridBad,
    Simulation.State.selectedCurve, Simulation.selectedTarget_real, Simulation.Coin.state,
    Simulation.State.table, initial]

/-- The actual ideal flag is exactly the pre-label grid collision event. The
postphase normalizes to one and erasing query logging preserves the real prefix law. -/
theorem idealFlagged_flag_marginal [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (scalar : ScalarField) (auxiliary : Aux) :
    (idealFlagged adversary parameter scalar auxiliary).map Prod.snd =
      (Simulation.Prefix.actualPrefix adversary parameter auxiliary).map fun result =>
        decide (Simulation.Prefix.gridBad result.2.2 result.2.1.1
          (checkedScalarMultiplication scalar result.2.1.1)) := by
  rw [idealFlagged_snd_coin]
  simp only [Simulation.Prefix.actualPrefix, Simulation.simulator, Simulation.stateTape,
    PMF.bind_map, PMF.map_bind, PMF.map_comp, Function.comp_def]
  apply congrArg ((PMF.uniformOfFintype Simulation.Coin).bind)
  funext coin
  exact coinGridFlag_prefix adversary parameter scalar auxiliary coin

/-- Unconditional bad-flag bound for the ACTUAL ideal flagged two-phase experiment. -/
theorem idealFlagged_bad_le [FieldCertificate] [GroupCertificate] [Fintype Block] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (scalar : ScalarField) (auxiliary : Aux) :
    (idealFlagged adversary parameter scalar auxiliary).toOuterMeasure {result | result.2 = true} ≤
      (12700 * adversary.firstQueryBudget parameter : Nat) / (Fintype.card Block : ℝ≥0∞) := by
  have law := congrArg (fun p : PMF Bool => p.toOuterMeasure {flag | flag = true})
    (idealFlagged_flag_marginal adversary parameter scalar auxiliary)
  simp only [PMF.toOuterMeasure_map_apply, Set.preimage_ofPred_eq, decide_eq_true_eq] at law
  rw [law]
  exact Simulation.Prefix.actualPrefix_grid_bad_le adversary parameter auxiliary
    (checkedScalarMultiplication scalar)

end
end Kriterion.DirectDisclosure.SourceKernel
