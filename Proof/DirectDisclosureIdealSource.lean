import Proof.DirectDisclosureEndpointMass
import Proof.DirectDisclosureSourceRequest

namespace Kriterion.DirectDisclosure.Endpoint

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section

/-- The actual ideal source is precisely one event of the simulator's original
uniform coin, retaining the full public table, selected labels, and both transcripts. -/
theorem idealSource_coin_event [FieldCertificate] [GroupCertificate] {Aux : Type}
    (parameter : Nat) (scalar : NonZeroScalar) (publicTable : Public)
    (selected : AffineInput × Aux) (labels : Garbling.Labels)
    (before after : List (Sigma Garbling.oracleSpec.Answer)) :
    idealSource parameter scalar publicTable selected labels before after =
      (PMF.uniformOfFintype Simulation.Coin).toOuterMeasure {coin |
        coin.state.table = publicTable ∧
        OracleTranscriptCompatible Simulation.handler coin.state before ∧
        (transcriptFinalState Simulation.handler coin.state before).labels selected.1 = labels ∧
        OracleTranscriptCompatible Simulation.handler
          ((transcriptFinalState Simulation.handler coin.state before).finish selected.1
            (checkedScalarMultiplication scalar.value selected.1)) after} := by
  unfold idealSource
  dsimp only [Simulation.simulator]
  rw [sampledTwoPhaseSourceMass_pure]
  simp only [Simulation.stateTape, PMF.map_comp, PMF.toOuterMeasure_map_apply]
  rfl

/-- Direct simulation forwards every public query to its complete three-oracle state. -/
theorem simulationTranscript_compatible (state : Simulation.State)
    (history : List (Sigma Garbling.oracleSpec.Answer)) :
    OracleTranscriptCompatible Simulation.handler state history ↔
      OracleTranscriptCompatible idealOracleHandler state.oracle history := by
  induction history generalizing state with
  | nil => rfl
  | cons entry tail ih =>
    rcases entry with ⟨query, answer⟩
    change _ ∧ _ ↔ _ ∧ _
    exact and_congr Iff.rfl (ih _)

/-- A prefix changes only the oracle state, preserving all private curve/key/target fields. -/
theorem simulationTranscript_final (state : Simulation.State)
    (history : List (Sigma Garbling.oracleSpec.Answer)) :
    transcriptFinalState Simulation.handler state history =
      {state with oracle := transcriptFinalState idealOracleHandler state.oracle history} := by
  induction history generalizing state with
  | nil => rfl
  | cons entry tail ih =>
    rcases entry with ⟨query, answer⟩
    change transcriptFinalState Simulation.handler (Simulation.handler query state).2 tail = _
    rw [ih]
    rfl

/-- The exact selected schedule uses the recovered embedded scalar on valid inputs,
and only the independent target on invalid inputs. -/
def coinSchedule [FieldCertificate] (scalar : ScalarField) (input : AffineInput)
    (coin : Simulation.Coin) : List GateDirective :=
  (coin.curve.request.retarget input (MaskSource.selectedTarget (embedScalar scalar) input coin.target)).schedule
    input (coin.inputKey.encodeAffine input)

/-- This normalized event is still the ACTUAL ideal source; only the simulator
record wrapper has been removed, with every oracle and transcript retained. -/
theorem idealSource_oracle_event [FieldCertificate] [GroupCertificate] {Aux : Type}
    (parameter : Nat) (scalar : NonZeroScalar) (publicTable : Public)
    (selected : AffineInput × Aux) (labels : Garbling.Labels)
    (before after : List (Sigma Garbling.oracleSpec.Answer)) :
    idealSource parameter scalar publicTable selected labels before after =
      (PMF.uniformOfFintype Simulation.Coin).toOuterMeasure {coin |
        coin.curve.request.table = publicTable ∧
        OracleTranscriptCompatible idealOracleHandler coin.state.oracle before ∧
        (⟨BitInput.ofAffine selected.1, coin.inputKey.encodeAffine selected.1⟩ : Garbling.Labels) = labels ∧
        OracleTranscriptCompatible idealOracleHandler
          (programGateSchedule (transcriptFinalState idealOracleHandler coin.state.oracle before)
            (coinSchedule scalar.value selected.1 coin)) after} := by
  rw [idealSource_coin_event]
  apply congrArg (PMF.toOuterMeasure (PMF.uniformOfFintype Simulation.Coin))
  ext coin
  simp only [Set.mem_setOf_eq, simulationTranscript_compatible, simulationTranscript_final]
  change _ ∧ _ ∧ _ ∧ OracleTranscriptCompatible idealOracleHandler
    (({coin.state with oracle := transcriptFinalState idealOracleHandler coin.state.oracle before}).finish
      selected.1 (checkedScalarMultiplication scalar.value selected.1)).oracle after ↔ _
  simp only [Simulation.State.finish, Simulation.State.hashState, Simulation.State.selectedCurve,
    Simulation.selectedTarget_real, Simulation.State.labels, Simulation.Coin.state,
    Simulation.State.table, coinSchedule]

end
end Kriterion.DirectDisclosure.Endpoint
