import Construction.DirectDisclosure
import Proof.ScalarRecovery
import Proof.Privacy.Distribution.PublicSample

namespace Kriterion.DirectDisclosure.Simulation

open BN254 Cryptography ArgoMAC ArgoMAC.Security
noncomputable section

attribute [local instance] publicInputMacKeyFintype ciphertextFintype Classical.propDecidable

/-- Only curve sources and oracle/key randomness are sampled; no scalar ciphertext exists. -/
structure Coin where
  curve : CurvePublicSample
  oracles : SimulatorOracleCoin
  inputKey : InputMacKey
  target : BaseField
deriving Fintype

structure State where
  oracle : SimulatorState
  curve : CurveGateRequest
  inputKey : InputMacKey
  target : BaseField

def Coin.state (coin : Coin) : State := {
  oracle := {
    fixedOracle := coin.oracles.fixedOracle
    encOracle := coin.oracles.encOracle
    hashOracle := coin.oracles.hashOracle
    fixedTranscript := []
    encTranscript := []
    hashTranscript := []
    commitments := []
    linking := none
    bad := false }
  curve := coin.curve.request
  inputKey := coin.inputKey
  target := coin.target }

def State.table (state : State) : Public :=
  state.curve.table

def State.labels (state : State) (input : AffineInput) : Garbling.Labels :=
  ⟨BitInput.ofAffine input, state.inputKey.encodeAffine input⟩

/-- The valid target is recovered from the allowed output; an invalid target stays uniform. -/
def State.selectedTarget [FieldCertificate] [GroupCertificate]
    (state : State) (input : AffineInput) (output : Option Point) : BaseField :=
  if OnCurve input then embedScalar (ScalarRecovery.recover input output) else state.target

def State.selectedCurve [FieldCertificate] [GroupCertificate]
    (state : State) (input : AffineInput) (output : Option Point) : CurveGateRequest :=
  state.curve.retarget input (state.selectedTarget input output)

/-- No hash or EncPRF point is programmed by the direct variant. -/
def State.hashState [FieldCertificate] [GroupCertificate] (state : State) (_input : AffineInput) (_output : Option Point) : SimulatorState :=
  state.oracle

def State.finish [FieldCertificate] [GroupCertificate]
    (state : State) (input : AffineInput) (output : Option Point) : State :=
  let initial := state.hashState input output
  let schedule := (state.selectedCurve input output).schedule input (state.labels input).inputMac
  { state with oracle := programGateSchedule initial schedule }

def State.view (state : State) : Garbling.EvaluationOracle :=
  (state.oracle.fixedOracle, state.oracle.encOracle, state.oracle.hashOracle)

def handler : OracleHandler Garbling.oracleSpec State
  | query, state =>
    let answered := idealOracleHandler query state.oracle
    (answered.1, { state with oracle := answered.2 })

/-- Every prior reply is recorded; all hash and EncPRF oracle values remain unchanged. -/
def Seen (state : SimulatorState) : Garbling.OracleQuery → Prop
  | .fixedForward index input => ∃ record ∈ state.fixedTranscript,
      record.index = index ∧ record.domain = input
  | .fixedInverse index output => ∃ record ∈ state.fixedTranscript,
      record.index = index ∧ record.range = output
  | .hash input => ∃ record ∈ state.hashTranscript, record.input = input
  | _ => True

private theorem seen_mono {first second : SimulatorState}
    (fixed : first.fixedTranscript ⊆ second.fixedTranscript)
    (hash : first.hashTranscript ⊆ second.hashTranscript)
    (query : Garbling.OracleQuery) (seen : Seen first query) : Seen second query := by
  cases query with
  | fixedForward index input =>
    obtain ⟨record, member, equal⟩ := seen
    exact ⟨record, fixed member, equal⟩
  | fixedInverse index output =>
    obtain ⟨record, member, equal⟩ := seen
    exact ⟨record, fixed member, equal⟩
  | encForward => trivial
  | encInverse => trivial
  | hash input =>
    obtain ⟨record, member, equal⟩ := seen
    exact ⟨record, hash member, equal⟩

private theorem fixedSlot_hashTranscript (state : SimulatorState)
    (location : Pipeline.FixedKeyLocation) (window : Nat)
    (slot : Pipeline.FixedKeySlot) (label block : Block) :
    (programFixedSlot state location window slot label block).hashTranscript = state.hashTranscript := by
  unfold programFixedSlot tryProgramFixed
  split <;> rfl

private theorem directive_hashTranscript (directive : GateDirective) (state : SimulatorState) :
    (directive.apply state).hashTranscript = state.hashTranscript := by
  unfold GateDirective.apply programGateForTarget programGate
  split <;> simp only [programHashGate, programPadGate, fixedSlot_hashTranscript]

private theorem schedule_hashTranscript (state : SimulatorState) (schedule : List GateDirective) :
    (programGateSchedule state schedule).hashTranscript = state.hashTranscript := by
  induction schedule generalizing state with
  | nil => rfl
  | cons directive tail ih => exact (ih (directive.apply state)).trans (directive_hashTranscript directive state)

private theorem hashState_fixed [FieldCertificate] [GroupCertificate] (state : State) (input : AffineInput) (output : Option Point) :
    (state.hashState input output).fixedTranscript = state.oracle.fixedTranscript := rfl

private theorem hashState_hash [FieldCertificate] [GroupCertificate] (state : State) (input : AffineInput) (output : Option Point) :
    state.oracle.hashTranscript ⊆ (state.hashState input output).hashTranscript := List.Subset.refl _

private theorem hashState_enc [FieldCertificate] [GroupCertificate] (state : State) (input : AffineInput) (output : Option Point) :
    (state.hashState input output).encOracle = state.oracle.encOracle := rfl

private theorem hashState_invariant [FieldCertificate] [GroupCertificate] (state : State) (input : AffineInput) (output : Option Point)
    (valid : SimulatorInvariant state.oracle) : SimulatorInvariant (state.hashState input output) := valid

theorem finish_invariant [FieldCertificate] [GroupCertificate]
    (state : State) (input : AffineInput) (output : Option Point)
    (valid : SimulatorInvariant state.oracle) : SimulatorInvariant (state.finish input output).oracle := by
  dsimp only [State.finish]
  exact programGateSchedule_preservesInvariant (state.hashState input output)
    ((state.selectedCurve input output).schedule input (state.labels input).inputMac)
    (hashState_invariant state input output valid)

private theorem answer_preserved {first second : State}
    (firstValid : SimulatorInvariant first.oracle) (secondValid : SimulatorInvariant second.oracle)
    (fixed : first.oracle.fixedTranscript ⊆ second.oracle.fixedTranscript)
    (hash : first.oracle.hashTranscript ⊆ second.oracle.hashTranscript)
    (enc : second.oracle.encOracle = first.oracle.encOracle)
    (query : Garbling.OracleQuery) (seen : Seen first.oracle query) :
    publicAnswer second.view query = publicAnswer first.view query := by
  cases query with
  | fixedForward index input =>
    obtain ⟨record, member, rfl, rfl⟩ := seen
    exact (secondValid.1 record (fixed member)).trans (firstValid.1 record member).symm
  | fixedInverse index output =>
    obtain ⟨record, member, rfl, rfl⟩ := seen
    exact ((Equiv.symm_apply_eq _).mpr (secondValid.1 record (fixed member)).symm).trans
      ((Equiv.symm_apply_eq _).mpr (firstValid.1 record member).symm).symm
  | encForward index input => simp only [publicAnswer, State.view, enc]; rfl
  | encInverse index output => simp only [publicAnswer, State.view, enc]; rfl
  | hash input =>
    obtain ⟨record, member, rfl⟩ := seen
    exact (secondValid.2.2.1 record (hash member)).trans (firstValid.2.2.1 record member).symm

theorem finish_preserves_seen [FieldCertificate] [GroupCertificate]
    (state : State) (input : AffineInput) (output : Option Point)
    (valid : SimulatorInvariant state.oracle) :
    ∀ query, Seen state.oracle query →
      Seen (state.finish input output).oracle query ∧
        publicAnswer (state.finish input output).view query = publicAnswer state.view query := by
  have fixed : state.oracle.fixedTranscript ⊆ (state.finish input output).oracle.fixedTranscript := by
    rw [← hashState_fixed state input output]
    exact programGateSchedule_preservesRecords _ _
  have hash : state.oracle.hashTranscript ⊆ (state.finish input output).oracle.hashTranscript := by
    change _ ⊆ (programGateSchedule _ _).hashTranscript
    rw [schedule_hashTranscript]
    exact hashState_hash state input output
  have enc : (state.finish input output).oracle.encOracle = state.oracle.encOracle :=
    (programGateSchedule_encOracle _ _).trans (hashState_enc state input output)
  intro query seen
  exact ⟨seen_mono fixed hash query seen,
    answer_preserved valid (finish_invariant state input output valid) fixed hash enc query seen⟩

private def defaultCoin : Coin := {
  curve := {
    coefficients := fun _ => 0
    tables := fun _ => Vector.replicate coordinateBitCount defaultBitAdaptorTable
    quotients := fun _ _ => defaultHashLiftQuotient
    targets := fun _ _ => 0 }
  oracles := defaultSimulatorCoin.oracles
  inputKey := defaultSimulatorCoin.inputKey
  target := 0 }

instance coinNonempty : Nonempty Coin := ⟨defaultCoin⟩

def stateTape (_parameter : Nat) (_topology : Unit) : PMF State :=
  (PMF.uniformOfFintype Coin).map Coin.state

def simulator [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.Simulator AffineInput (Option Point) Public Garbling.Labels Unit State := {
  simulateGarble := fun parameter topology => (stateTape parameter topology).map fun state => (state.table, state)
  simulateEncode := fun state input output => PMF.pure (state.labels input, state.finish input output) }

theorem oracleSimulation [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.OracleSimulation simulator handler State.view := by
  refine ⟨fun state => SimulatorInvariant state.oracle, fun state query => Seen state.oracle query, ?_, ?_, ?_⟩
  · intro parameter topology result member
    dsimp only [simulator] at member
    rw [PMF.support_map] at member
    obtain ⟨state, stateMember, rfl⟩ := member
    dsimp only [stateTape] at stateMember
    rw [PMF.support_map] at stateMember
    obtain ⟨coin, _, rfl⟩ := stateMember
    simp [Coin.state, SimulatorInvariant, PermutationTranscriptMatches, HashTranscriptMatches, DistinctCommitments]
  · intro query state valid
    refine ⟨by cases query <;> rfl, by cases query <;> rfl,
      idealOracleHandler_preservesInvariant query state.oracle valid, ?_, ?_⟩
    · cases query <;> simp [Seen, handler, idealOracleHandler, oracleHandlerFor, recordFixed, recordEnc, recordHash]
    · intro prior seen
      apply seen_mono (query := prior) ?_ ?_ seen
      · cases query <;> simp [handler, idealOracleHandler, oracleHandlerFor, recordFixed, recordEnc, recordHash]
      · cases query <;> simp [handler, idealOracleHandler, oracleHandlerFor, recordFixed, recordEnc, recordHash]
  · intro state input output result valid member
    dsimp only [simulator] at member
    have equal := (PMF.mem_support_pure_iff _ _).mp member
    subst result
    exact ⟨finish_invariant state input output valid, finish_preserves_seen state input output valid⟩

end
end Kriterion.DirectDisclosure.Simulation
