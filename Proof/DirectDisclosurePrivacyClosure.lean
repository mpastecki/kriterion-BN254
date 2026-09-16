import Proof.DirectDisclosureFlaggedPointwise
import Proof.DirectDisclosureFlaggedBad
import Proof.DirectDisclosurePrivacyBridge

namespace Kriterion.DirectDisclosure.PrivacyClosure
open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section

/-- The remaining actual source comparison, stated on full transcripts and the false flag. -/
def SmallPointwiseBounds [FieldCertificate] [GroupCertificate] {Aux : Type}
    (witness : Garbling.Randomness) : Prop :=
  ∀ (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux),
    adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter < 2 ^ 100 →
    ∀ transcript : SourceKernel.Transcript adversary.State,
      (1 - (2 * ((adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter : Nat) : ℝ≥0∞) /
        (2 : ℝ≥0∞) ^ 128)) *
        SourceKernel.fullFlagged adversary parameter scalar.value auxiliary (transcript, false) ≤
      realAdaptiveTranscriptWithState internalScheme (randomTape witness) Garbling.oracleHandler
        adversary parameter scalar auxiliary transcript

/-- Exact source ratios imply all event bounds after accounting for the actual
ideal collision event and both uses of the checked global transport. -/
theorem small_events_of_pointwise [FieldCertificate] [GroupCertificate] {Aux : Type}
    (witness : Garbling.Randomness) (ratios : SmallPointwiseBounds (Aux := Aux) witness) :
    PrivacyBridge.SmallEventBounds (Aux := Aux) witness := by
  let : Fintype Block := Fintype.ofFinite Block
  intro adversary parameter scalar auxiliary small event
  let q := adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter
  let loss : ℝ≥0∞ := 2 * (q : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128
  let transfer : ℝ := 1 / (baseFieldModulus : ℝ) +
    (1270 : ℝ) * (2 ^ 384 % baseFieldModulus : Nat) / (2 : ℝ) ^ 384
  let prefixLoss : ℝ := 12700 * (adversary.firstQueryBudget parameter : ℝ) / (2 : ℝ) ^ 128
  let real := realAdaptiveTranscriptWithState internalScheme (randomTape witness) Garbling.oracleHandler
    adversary parameter scalar auxiliary
  let ideal := idealAdaptiveTranscriptWithState internalScheme topology Simulation.simulator Simulation.handler
    adversary parameter scalar auxiliary
  let flagged := SourceKernel.fullFlagged adversary parameter scalar.value auxiliary
  let idealFlag := SourceKernel.idealFlagged adversary parameter scalar.value auxiliary
  have lossSmall : loss ≤ 1 := by
    have queries : (q : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ 100 := by
      exact_mod_cast (Nat.le_of_lt small)
    calc
      loss ≤ 2 * (2 : ℝ≥0∞) ^ 100 / (2 : ℝ≥0∞) ^ 128 :=
        ENNReal.div_le_div_right (by gcongr) _
      _ ≤ 1 := by
        rw [ENNReal.div_le_iff (by norm_num) (by simp)]
        norm_num
  have goodBound (e : Set (SourceKernel.Transcript adversary.State)) :
      (1 - loss.toReal) * (flagged.toOuterMeasure (EventDistance.good e)).toReal ≤
        (real.toOuterMeasure e).toReal :=
    EventDistance.pointwise_good_event_real real flagged loss lossSmall
      (ratios adversary parameter scalar auxiliary small) e
  have actualBad : (idealFlag.toOuterMeasure EventDistance.bad).toReal ≤ prefixLoss := by
    have card : Fintype.card Block = 2 ^ 128 :=
      (Fintype.card_congr BitVec.equivFin.toEquiv).trans (Fintype.card_fin _)
    have bound := SourceKernel.idealFlagged_bad_le adversary parameter scalar.value auxiliary
    rw [card] at bound
    have converted := ENNReal.toReal_mono (by finiteness) bound
    simpa only [idealFlag, EventDistance.bad, prefixLoss, ENNReal.toReal_div,
      ENNReal.toReal_natCast, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat] using converted
  have badBound : (flagged.toOuterMeasure EventDistance.bad).toReal ≤ prefixLoss + transfer := by
    have distance := SourceKernel.flagged_transport_bound adversary parameter scalar.value auxiliary EventDistance.bad
    change |(idealFlag.toOuterMeasure EventDistance.bad).toReal -
      (flagged.toOuterMeasure EventDistance.bad).toReal| ≤ transfer at distance
    linarith [(abs_le.mp distance).1]
  have transport (e : Set (SourceKernel.Transcript adversary.State)) :
      |((flagged.map Prod.fst).toOuterMeasure e).toReal - (ideal.toOuterMeasure e).toReal| ≤ transfer := by
    have projection := SourceKernel.idealFlagged_projection adversary parameter scalar auxiliary
    change idealFlag.map Prod.fst = ideal at projection
    rw [← projection, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply, abs_sub_comm]
    exact SourceKernel.flagged_transport_bound adversary parameter scalar.value auxiliary (Prod.fst ⁻¹' e)
  have estimate := EventDistance.flagged_event_distance real ideal flagged loss.toReal
    (prefixLoss + transfer) transfer ENNReal.toReal_nonneg goodBound badBound transport event
  convert estimate using 1
  simp only [loss, q, prefixLoss, transfer, ENNReal.toReal_div, ENNReal.toReal_mul,
    ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  ring

/-- Supplying the actual source inequality completes the unchanged universal game. -/
theorem privacy_of_pointwise [FieldCertificate] [GroupCertificate] {Aux : Type}
    (witness : Garbling.Randomness) (ratios : SmallPointwiseBounds (Aux := Aux) witness) :
    GarbledCircuit.ConcreteAdaptivePrivacy (Aux := Aux) internalScheme topology Simulation.simulator
      (randomTape witness) Garbling.oracleHandler Simulation.handler 100 :=
  PrivacyBridge.privacy_of_small_event_bounds witness (small_events_of_pointwise witness ratios)

end
end Kriterion.DirectDisclosure.PrivacyClosure
