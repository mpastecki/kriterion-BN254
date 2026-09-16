import Proof.DirectDisclosureSelectedKey
import Proof.DirectDisclosureOracleSplit

namespace Kriterion.DirectDisclosure.Endpoint

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable transcriptOracleFintype

abbrev OracleRest := Simulation.OracleSplit.Rest
abbrev FixedOracle := Simulation.OracleSplit.FixedOracle

def restInitial (rest : OracleRest) (oracle : FixedOracle) : SimulatorState :=
  (Simulation.OracleSplit.restore rest oracle).state.oracle

def restSchedule [FieldCertificate] (scalar : ScalarField) (input : AffineInput)
    (rest : OracleRest) : List GateDirective :=
  (rest.curve.request.retarget input (MaskSource.selectedTarget (embedScalar scalar) input rest.target)).schedule
    input (rest.inputKey.encodeAffine input)

def restOracleMass [FieldCertificate] (scalar : ScalarField) (input : AffineInput)
    (rest : OracleRest) (before after : List (Sigma Garbling.oracleSpec.Answer)) : ℝ≥0∞ :=
  (PMF.uniformOfFintype FixedOracle).toOuterMeasure {oracle |
    OracleTranscriptCompatible idealOracleHandler (restInitial rest oracle) before ∧
      OracleTranscriptCompatible idealOracleHandler
        (programGateSchedule (transcriptFinalState idealOracleHandler (restInitial rest oracle) before)
          (restSchedule scalar input rest)) after}

private theorem fixed_conditions {A : Type*} (samples : PMF A) (P Q : Prop) (first second : A → Prop) :
    samples.toOuterMeasure {value | P ∧ first value ∧ Q ∧ second value} =
      if P ∧ Q then samples.toOuterMeasure {value | first value ∧ second value} else 0 := by
  by_cases p : P <;> by_cases q : Q <;> simp [p, q]

/-- The ACTUAL ideal source splits into retained nonfixed data and the fixed-oracle
prefix/program/postquery event. Public-table and selected-label constraints are exact. -/
theorem idealSource_rest_split [FieldCertificate] [GroupCertificate] {Aux : Type}
    (parameter : Nat) (scalar : NonZeroScalar) (publicTable : Public)
    (selected : AffineInput × Aux) (labels : Garbling.Labels)
    (before after : List (Sigma Garbling.oracleSpec.Answer)) :
    idealSource parameter scalar publicTable selected labels before after =
      ∑' rest : OracleRest, (Fintype.card OracleRest : ℝ≥0∞)⁻¹ *
        if rest.curve.request.table = publicTable ∧
          (⟨BitInput.ofAffine selected.1, rest.inputKey.encodeAffine selected.1⟩ : Garbling.Labels) = labels
        then restOracleMass scalar.value selected.1 rest before after else 0 := by
  rw [idealSource_oracle_event, Simulation.OracleSplit.uniform_event]
  apply tsum_congr
  intro rest
  apply congrArg ((Fintype.card OracleRest : ℝ≥0∞)⁻¹ * ·)
  simp only [Simulation.OracleSplit.restore, Simulation.Coin.state, coinSchedule,
    restOracleMass, restInitial, restSchedule]
  exact fixed_conditions (PMF.uniformOfFintype FixedOracle) _ _ _ _

/-- This is the actual retained fixed-oracle event conditioned on all prior replies.
The witness only supplies the already inhabited real-tape type; no oracle assumption is added. -/
theorem restOracleMass_conditioned [FieldCertificate]
    (witness : Garbling.Randomness) (scalar : ScalarField) (input : AffineInput)
    (rest : OracleRest) (reference : FixedOracle)
    (before after : List (Sigma Garbling.oracleSpec.Answer))
    (compatible : OracleTranscriptCompatible idealOracleHandler (restInitial rest reference) before)
    [Nonempty (TranscriptOracle
      (transcriptFinalState idealOracleHandler (restInitial rest reference) before).fixedTranscript)] :
    restOracleMass scalar input rest before after =
      fixedTranscriptFactor (transcriptFinalState idealOracleHandler (restInitial rest reference) before).fixedTranscript *
        ((PMF.uniformOfFintype (TranscriptOracle
          (transcriptFinalState idealOracleHandler (restInitial rest reference) before).fixedTranscript)).map
            (fun oracle => programGateSchedule
              {transcriptFinalState idealOracleHandler (restInitial rest reference) before with fixedOracle := oracle.1}
              (restSchedule scalar input rest))).toOuterMeasure
                {programmed | OracleTranscriptCompatible idealOracleHandler programmed after} := by
  have law := idealPrefixProgrammed_mass (restInitial rest reference)
    {witness with encPRFOracle := rest.encOracle, hashOracle := rest.hashOracle}
    before after (restSchedule scalar input rest) rfl rfl rfl compatible
  exact law

end
end Kriterion.DirectDisclosure.Endpoint
