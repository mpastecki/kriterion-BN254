import Proof.DirectDisclosureSourceKernel
import Proof.DirectDisclosureNumericBound

namespace Kriterion.DirectDisclosure.PrivacyBridge
open BN254 Cryptography Cryptography.Assumptions ArgoMAC ArgoMAC.Security
noncomputable section

/-- The actual decision advantage is the full-transcript decision event difference. -/
theorem adaptiveTranscriptWithState_advantage_eq
    {oracle : OracleSpec.{0, 0}} {Circuit Input Output Randomness Public EncodingKey Labels
      EvaluationOracle Topology State Aux : Type}
    (scheme : GarbledCircuit Circuit Input Output Randomness Public EncodingKey Labels EvaluationOracle)
    (randomTape : Nat → PMF Randomness) (realOracle : OracleHandler oracle Randomness)
    (topology : Circuit → Topology)
    (simulator : GarbledCircuit.Simulator Input Output Public Labels Topology State)
    (idealOracle : OracleHandler oracle State)
    (adversary : GarbledCircuit.AdaptiveAdversary oracle Input Public Labels Aux)
    (parameter : Nat) (circuit : Circuit) (auxiliary : Aux) :
    advantage (GarbledCircuit.realGame scheme randomTape realOracle adversary parameter circuit auxiliary)
      (GarbledCircuit.idealGame scheme topology simulator idealOracle adversary parameter circuit auxiliary) =
    |((realAdaptiveTranscriptWithState scheme randomTape realOracle adversary parameter circuit auxiliary).toOuterMeasure
        {output | output.2.2.2.2.1 = true}).toReal -
      ((idealAdaptiveTranscriptWithState scheme topology simulator idealOracle adversary parameter circuit auxiliary).toOuterMeasure
        {output | output.2.2.2.2.1 = true}).toReal| := by
  have realDecision : (realAdaptiveTranscriptWithState scheme randomTape realOracle adversary
      parameter circuit auxiliary).map (fun output => output.2.2.2.2.1) =
      GarbledCircuit.realGame scheme randomTape realOracle adversary parameter circuit auxiliary := by
    rw [← realAdaptiveTranscript_decision scheme randomTape realOracle adversary parameter circuit auxiliary,
      ← realAdaptiveTranscriptWithState_erase scheme randomTape realOracle adversary parameter circuit auxiliary,
      PMF.map_comp]
    rfl
  have idealDecision : (idealAdaptiveTranscriptWithState scheme topology simulator idealOracle adversary
      parameter circuit auxiliary).map (fun output => output.2.2.2.2.1) =
      GarbledCircuit.idealGame scheme topology simulator idealOracle adversary parameter circuit auxiliary := by
    rw [← idealAdaptiveTranscript_decision scheme topology simulator idealOracle adversary parameter circuit auxiliary,
      ← idealAdaptiveTranscriptWithState_erase scheme topology simulator idealOracle adversary parameter circuit auxiliary,
      PMF.map_comp]
    rfl
  unfold advantage
  rw [← PMF.toOuterMeasure_apply_singleton, ← PMF.toOuterMeasure_apply_singleton,
    ← realDecision, ← idealDecision, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  rfl


/-- The exact small-budget event obligation needed to close the fixed privacy game. -/
def SmallEventBounds [FieldCertificate] [GroupCertificate] {Aux : Type}
    (witness : Garbling.Randomness) : Prop :=
  ∀ (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux),
    adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 100 →
    ∀ event : Set (SourceKernel.Transcript adversary.State),
      |((realAdaptiveTranscriptWithState internalScheme (randomTape witness) Garbling.oracleHandler
        adversary parameter scalar auxiliary).toOuterMeasure event).toReal -
        ((idealAdaptiveTranscriptWithState internalScheme topology Simulation.simulator Simulation.handler
        adversary parameter scalar auxiliary).toOuterMeasure event).toReal| ≤
      (2 * ((adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter : Nat) : ℝ) / (2 : ℝ) ^ 128) +
      (12700 * (adversary.firstQueryBudget parameter : ℝ) / (2 : ℝ) ^ 128) +
      2 / (baseFieldModulus : ℝ) +
      2 * (1270 * (2 ^ 384 % baseFieldModulus : Nat) / (2 : ℝ) ^ 384)

/-- A supplied complete small-budget event estimate closes every query budget.
No event estimate is asserted by this bridge. -/
theorem privacy_of_small_event_bounds [FieldCertificate] [GroupCertificate] {Aux : Type}
    (witness : Garbling.Randomness) (bound : SmallEventBounds (Aux := Aux) witness) :
    GarbledCircuit.ConcreteAdaptivePrivacy (Aux := Aux) internalScheme topology Simulation.simulator
      (randomTape witness) Garbling.oracleHandler Simulation.handler 100 := by
  intro adversary circuits auxiliaries parameter
  let queries := adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter
  change WorkPerAdvantage 100 (queries + 1) _
  by_cases small : queries < 2 ^ 100
  · unfold WorkPerAdvantage
    rw [adaptiveTranscriptWithState_advantage_eq]
    have estimate := bound adversary parameter (circuits parameter) (auxiliaries parameter) small
      {output | output.2.2.2.2.1 = true}
    apply (mul_le_mul_of_nonneg_right estimate (by positivity : 0 ≤ (2 : ℝ) ^ 100)).trans
    simpa only [queries, Nat.cast_add, Nat.cast_one] using
      numeric_work_bound (adversary.firstQueryBudget parameter) queries (Nat.le_add_right _ _)
  · exact largeBudget_has100Bits _ _ queries (Nat.le_of_not_gt small)

end
end Kriterion.DirectDisclosure.PrivacyBridge
