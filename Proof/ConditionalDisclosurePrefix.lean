import Proof.ConditionalDisclosureSimulator
import Proof.Privacy.Distribution.PublicDistribution

namespace Kriterion.ConditionalDisclosure.Simulation.Prefix

open BN254 Cryptography ArgoMAC ArgoMAC.Security
noncomputable section
attribute [local instance] publicInputMacKeyFintype ciphertextFintype

abbrev Frame := CurvePublicSample × SimulatorOracleCoin × Ciphertext
abbrev Secret := InputMacKey × BaseField

/-- The simulator's independent key and target are separated from every frame value. -/
def coinEquiv : Coin ≃ Secret × Frame where
  toFun coin := ((coin.inputKey, coin.target), (coin.curve, coin.oracles, coin.ciphertext))
  invFun value := {
    curve := value.2.1
    oracles := value.2.2.1
    inputKey := value.1.1
    target := value.1.2
    ciphertext := value.2.2.2 }
  left_inv coin := by cases coin; rfl
  right_inv value := by rcases value with ⟨⟨key, target⟩, curve, oracles, ciphertext⟩; rfl

instance frameNonempty : Nonempty Frame :=
  ⟨(coinEquiv (Classical.choice (inferInstance : Nonempty Coin))).2⟩
instance secretNonempty : Nonempty Secret :=
  ⟨(coinEquiv (Classical.choice (inferInstance : Nonempty Coin))).1⟩

def initialOracle (frame : Frame) : SimulatorState := {
  fixedOracle := frame.2.1.fixedOracle
  encOracle := frame.2.1.encOracle
  hashOracle := frame.2.1.hashOracle
  fixedTranscript := []
  encTranscript := []
  hashTranscript := []
  commitments := []
  linking := none
  bad := false }

def restore (frame : Frame) (secret : Secret) (oracle : SimulatorState) : Simulation.State := {
  oracle := oracle
  curve := frame.1.request
  inputKey := secret.1
  target := secret.2
  ciphertext := frame.2.2 }

def frameTable (frame : Frame) : Public := ⟨frame.1.request.table, frame.2.2⟩

/-- All prefix queries operate solely on the oracle state; the secret fields are retained. -/
theorem run_restore {Result : Type*} {budget : Nat}
    (frame : Frame) (secret : Secret) (program : OracleProgram Garbling.oracleSpec Result budget)
    (oracle : SimulatorState) :
    (program.run idealOracleHandler oracle).map (fun result => (result.1, restore frame secret result.2)) =
      program.run Simulation.handler (restore frame secret oracle) := by
  apply OracleProgram.run_project idealOracleHandler Simulation.handler (restore frame secret)
  intro query state
  exact ⟨rfl, rfl⟩

def coinKernel {Aux : Type*}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (coin : Coin) :
    PMF (Public × (AffineInput × adversary.State) × Simulation.State) :=
  ((adversary.chooseInput parameter coin.state.table auxiliary).run Simulation.handler coin.state).map
    (fun selected => (coin.state.table, selected.1, selected.2))

theorem coinKernel_frame {Aux : Type*}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (frame : Frame) (secret : Secret) :
    coinKernel adversary parameter auxiliary (coinEquiv.symm (secret, frame)) =
      ((adversary.chooseInput parameter (frameTable frame) auxiliary).run idealOracleHandler
        (initialOracle frame)).map
          (fun selected => (frameTable frame, selected.1, restore frame secret selected.2)) := by
  change ((adversary.chooseInput parameter (frameTable frame) auxiliary).run Simulation.handler
    (restore frame secret (initialOracle frame))).map
      (fun selected => (frameTable frame, selected.1, selected.2)) = _
  rw [← run_restore, PMF.map_comp]
  rfl

def actualPrefix [FieldCertificate] [GroupCertificate] {Aux : Type*}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) :
    PMF (Public × (AffineInput × adversary.State) × Simulation.State) :=
  (simulator.simulateGarble parameter ()).bind fun initial =>
    ((adversary.chooseInput parameter initial.1 auxiliary).run Simulation.handler initial.2).map
      (fun selected => (initial.1, selected.1, selected.2))

def separatedPrefix {Aux : Type*}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) :
    PMF (Public × (AffineInput × adversary.State) × Simulation.State) :=
  (PMF.uniformOfFintype Frame).bind fun frame =>
    ((adversary.chooseInput parameter (frameTable frame) auxiliary).run idealOracleHandler
      (initialOracle frame)).bind fun selected =>
      (PMF.uniformOfFintype Secret).map fun secret =>
        (frameTable frame, selected.1, restore frame secret selected.2)

private theorem actualPrefix_coin [FieldCertificate] [GroupCertificate] {Aux : Type*}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) :
    actualPrefix adversary parameter auxiliary =
      (PMF.uniformOfFintype Coin).bind (coinKernel adversary parameter auxiliary) := by
  simp only [actualPrefix, simulator, stateTape, PMF.bind_map]
  rfl

private theorem bind_map_comm {A B C : Type*} (p : PMF A) (q : PMF B) (f : A → B → C) :
    (p.bind fun a => q.map (f a)) = q.bind fun b => p.map (fun a => f a b) :=
  PMF.bind_comm p q (fun a b => PMF.pure (f a b))

/-- The actual simulator prefix leaves key and target exactly uniform and independent
of its public table, chosen input, adversary state and complete oracle transcript. -/
theorem actualPrefix_factorization [FieldCertificate] [GroupCertificate] {Aux : Type*}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) :
    actualPrefix adversary parameter auxiliary = separatedPrefix adversary parameter auxiliary := by
  rw [actualPrefix_coin, ← map_uniformOfFintype_equivBetween coinEquiv.symm, PMF.bind_map,
    uniform_prod_eq_bind, PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def, coinKernel_frame, separatedPrefix]
  apply congrArg ((PMF.uniformOfFintype Frame).bind)
  funext frame
  exact bind_map_comm _ _ _

end
end Kriterion.ConditionalDisclosure.Simulation.Prefix
