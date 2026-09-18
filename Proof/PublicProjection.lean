import Construction.PublicProjection
import Security.AdaptivePrivacy

namespace Kriterion.PublicProjection
open Cryptography GarbledCircuit

/-- The simulator keeps its original private state and projects only published data. -/
noncomputable def simulator {Input Output Public NewPublic Labels Topology State : Type}
    (original : Simulator Input Output Public Labels Topology State) (project : Public → NewPublic) :
    Simulator Input Output NewPublic Labels Topology State where
  simulateGarble parameter topology := (original.simulateGarble parameter topology).map
    (fun result => (project result.1, result.2))
  simulateEncode := original.simulateEncode

/-- Public projection preserves every prior-query and oracle-state obligation. -/
theorem oracleSimulation {FixedIndex EncIndex Input Output Public NewPublic Labels Topology State : Type}
    (original : Simulator Input Output Public Labels Topology State) (project : Public → NewPublic)
    (handler : OracleHandler (publicOracleSpec FixedIndex EncIndex) State)
    (view : State → PublicOracle FixedIndex EncIndex)
    (rules : OracleSimulation original handler view) :
    OracleSimulation (simulator original project) handler view := by
  obtain ⟨valid, seen, initial, query, encode⟩ := rules
  refine ⟨valid, seen, ?_, query, encode⟩
  intro parameter topology result member
  dsimp only [simulator] at member
  rw [PMF.support_map] at member
  obtain ⟨originalResult, originalMember, rfl⟩ := member
  exact initial parameter topology originalResult originalMember

/-- Deterministic public projection inherits the complete two-stage game with
exactly the same public queries and work count. No inverse projection is required. -/
theorem adaptivePrivacy {oracle : OracleSpec}
    {Circuit Input Output Randomness Public NewPublic Key Labels Oracle Topology State Aux : Type}
    (original : GarbledCircuit Circuit Input Output Randomness Public Key Labels Oracle)
    (project : Public → NewPublic)
    (evaluate : Oracle → NewPublic → Input → Labels → Option Output)
    (topology : Circuit → Topology) (originalSimulator : Simulator Input Output Public Labels Topology State)
    (randomTape : Nat → PMF Randomness) (realOracle : OracleHandler oracle Randomness)
    (idealOracle : OracleHandler oracle State) (bits : Nat)
    (privacy : ConcreteAdaptivePrivacy (Aux := Aux) original topology originalSimulator randomTape
      realOracle idealOracle bits) :
    ConcreteAdaptivePrivacy (Aux := Aux) (scheme original project evaluate) topology
      (simulator originalSimulator project) randomTape realOracle idealOracle bits := by
  intro adversary circuits auxiliaries parameter
  let lifted : AdaptiveAdversary oracle Input Public Labels Aux := {
    State := adversary.State
    firstQueryBudget := adversary.firstQueryBudget
    secondQueryBudget := adversary.secondQueryBudget
    chooseInput := fun parameter table => adversary.chooseInput parameter (project table)
    decide := fun parameter table => adversary.decide parameter (project table) }
  simpa only [ConcreteAdaptivePrivacy, realGame, idealGame, scheme, simulator,
    PMF.bind_map, Function.comp_def, adversaryWork, lifted] using
    privacy lifted circuits auxiliaries parameter

end Kriterion.PublicProjection
