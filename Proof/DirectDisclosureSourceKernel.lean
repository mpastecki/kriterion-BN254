import Proof.DirectDisclosureIdealSource
import Proof.DirectDisclosurePrefix

namespace Kriterion.DirectDisclosure.SourceKernel

open BN254 Cryptography ArgoMAC ArgoMAC.Security
noncomputable section

abbrev Transcript (State : Type) := Public × (AffineInput × State) ×
  List (Sigma Garbling.oracleSpec.Answer) × Garbling.Labels × Bool × List (Sigma Garbling.oracleSpec.Answer)
abbrev Choice (State : Type) := AffineInput × (Public × State × SimulatorState × List (Sigma Garbling.oracleSpec.Answer))

def initial (oracles : SimulatorOracleCoin) : SimulatorState := {
  fixedOracle := oracles.fixedOracle
  encOracle := oracles.encOracle
  hashOracle := oracles.hashOracle
  fixedTranscript := []
  encTranscript := []
  hashTranscript := []
  commitments := []
  linking := none
  bad := false }

def choose {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (table : Public) (oracles : SimulatorOracleCoin) :
    PMF (Choice adversary.State) :=
  (runOracleProgramWithTranscript idealOracleHandler
    (adversary.chooseInput parameter table auxiliary) (initial oracles)).map fun output =>
      (output.1.1, table, output.1.2, output.2.1, output.2.2)

def observe {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (key : InputMacKey)
    (choice : Choice adversary.State) (request : CurveGateRequest) : PMF (Transcript adversary.State) :=
  let labels : Garbling.Labels := ⟨BitInput.ofAffine choice.1, key.encodeAffine choice.1⟩
  let programmed := programGateSchedule choice.2.2.2.1 (request.schedule choice.1 labels.inputMac)
  (runOracleProgramWithTranscript idealOracleHandler
    (adversary.decide parameter choice.2.1 labels auxiliary choice.2.2.1) programmed).map fun output =>
      (choice.2.1, (choice.1, choice.2.2.1), choice.2.2.2.2, labels, output.1, output.2.2)

def run {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (table : Public) (oracles : SimulatorOracleCoin)
    (key : InputMacKey) (request : AffineInput → CurveGateRequest) : PMF (Transcript adversary.State) :=
  (choose adversary parameter auxiliary table oracles).bind fun choice =>
    observe adversary parameter auxiliary key choice (request choice.1)

def ideal [FieldCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (scalar : ScalarField) (auxiliary : Aux) (coin : Simulation.Coin) :
    PMF (Transcript adversary.State) :=
  run adversary parameter auxiliary coin.curve.request.table coin.oracles coin.inputKey fun input =>
    coin.curve.request.retarget input (MaskSource.selectedTarget (embedScalar scalar) input coin.target)

/-- Exact query logging commutes with removal of the simulator's private record wrapper. -/
theorem transcript_lift {Result : Type} {budget : Nat}
    (program : OracleProgram Garbling.oracleSpec Result budget) (state : Simulation.State) :
    runOracleProgramWithTranscript Simulation.handler program state =
      (runOracleProgramWithTranscript idealOracleHandler program state.oracle).map fun output =>
        (output.1, {state with oracle := output.2.1}, output.2.2) := by
  induction program generalizing state with
  | pure distribution => simp only [runOracleProgramWithTranscript_pure, PMF.map_comp]; rfl
  | query query next ih =>
    simp only [runOracleProgramWithTranscript_query, ih, PMF.map_comp]
    rfl
  | sample distribution next ih =>
    simp only [runOracleProgramWithTranscript_sample, ih, PMF.map_bind]

/-- The exact actual ideal transcript is the direct two-phase curve-source kernel,
including both query histories and selected adversary state. -/
theorem actual_ideal_transcript [FieldCertificate] [GroupCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :
    idealAdaptiveTranscriptWithState internalScheme topology Simulation.simulator Simulation.handler
      adversary parameter scalar auxiliary =
      (PMF.uniformOfFintype Simulation.Coin).bind (ideal adversary parameter scalar.value auxiliary) := by
  simp only [idealAdaptiveTranscriptWithState, sampledTwoPhaseTranscript, Simulation.simulator,
    Simulation.stateTape, PMF.bind_map]
  apply congrArg ((PMF.uniformOfFintype Simulation.Coin).bind)
  funext coin
  simp only [twoPhaseTranscript, transcript_lift, PMF.bind_map, PMF.pure_bind, PMF.map_comp,
    PMF.map_bind]
  unfold ideal run choose observe
  simp only [PMF.bind_map, PMF.map_comp]
  simp only [Function.comp_def, Simulation.Coin.state, Simulation.State.table]
  apply congrArg ((runOracleProgramWithTranscript idealOracleHandler
    (adversary.chooseInput parameter coin.curve.request.table auxiliary) (initial coin.oracles)).bind)
  funext selected
  simp only [PMF.map_comp, Function.comp_def, Simulation.State.finish, Simulation.State.hashState, Simulation.State.selectedCurve,
    Simulation.selectedTarget_real, Simulation.State.labels, Simulation.State.table,
    Simulation.Coin.state, internalScheme, initial]

end
end Kriterion.DirectDisclosure.SourceKernel
