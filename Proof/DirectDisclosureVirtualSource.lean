import Proof.DirectDisclosureFlaggedKernel
import Proof.DirectDisclosureSourceProduct
import Proof.DirectDisclosureFlaggedMass

namespace Kriterion.DirectDisclosure.SourceKernel

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable bitAdaptorTableFintype publicInputMacKeyFintype
local instance : Nonempty NonZeroBase := ⟨⟨1, by decide⟩⟩
local instance : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
local instance : Nonempty SimulatorOracleCoin := ⟨defaultSimulatorCoin.oracles⟩
local instance : Nonempty Randomness.Seed :=
  ⟨⟨⟨1, by decide⟩, 0, 0, defaultSimulatorCoin.oracles, defaultSimulatorCoin.inputKey⟩⟩
local instance : Nonempty Randomness.SourceProduct.Ambient :=
  ⟨⟨⟨1, by decide⟩, defaultSimulatorCoin.oracles, defaultSimulatorCoin.inputKey⟩⟩
local instance : Nonempty ConditionalDisclosure.CurveSource.FullSource :=
  ⟨(fun _ => 0, fun _ => defaultBitAdaptorTable)⟩
local instance : Nonempty Randomness.SourceProduct.TagSource :=
  ⟨(fun _ => 0, fun _ => 0, fun _ => defaultBitAdaptorTable)⟩

abbrev FullTag := ConditionalDisclosure.CurveSource.FullSource
abbrev TapeSource := Garbling.Randomness × FullTag

def sourceOf (seed : Randomness.Seed) (tag : FullTag) : CurveMaskSample :=
  ConditionalDisclosure.CurveSource.decodeTag seed.r1 seed.r2 tag

def tableOf (scalar : ScalarField) (seed : Randomness.Seed) (tag : FullTag) : Public :=
  ConditionalDisclosure.CurveSource.sourceTable (embedScalar scalar) seed.mask.value (sourceOf seed tag)

def requestOf (scalar : ScalarField) (seed : Randomness.Seed) (tag : FullTag) (input : AffineInput) : CurveGateRequest :=
  (curveMaskSampleGarble (embedScalar scalar) seed.mask.value input (sourceOf seed tag)).request

def seedKernel {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (scalar : ScalarField) (auxiliary : Aux)
    (seed : Randomness.Seed) (tag : FullTag) : PMF (Transcript adversary.State × Bool) :=
  (choose adversary parameter auxiliary (tableOf scalar seed tag) seed.oracles).bind fun choice =>
    flagObserve adversary parameter auxiliary (decide (¬ ConditionalDisclosure.CurveSource.Complete tag.1))
      (choice.1, seed.oracles, seed.inputKey, choice.2) (requestOf scalar seed tag choice.1)

private theorem restored_source (ambient : Randomness.SourceProduct.Ambient)
    (full : Randomness.SourceProduct.TagSource) :
    sourceOf (Randomness.SourceProduct.sourceEquiv.symm (ambient, full)).1
      (Randomness.SourceProduct.sourceEquiv.symm (ambient, full)).2 =
      ConditionalDisclosure.CurveSource.decode full := by
  change ConditionalDisclosure.CurveSource.decode (full.1, ![full.2.1 0, full.2.1 1], full.2.2) = _
  have eta : ![full.2.1 0, full.2.1 1] = full.2.1 := by funext i; fin_cases i <;> rfl
  rw [eta]

private theorem restored_kernel {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (scalar : ScalarField) (auxiliary : Aux)
    (ambient : Randomness.SourceProduct.Ambient) (full : Randomness.SourceProduct.TagSource) :
    seedKernel adversary parameter scalar auxiliary
      (Randomness.SourceProduct.sourceEquiv.symm (ambient, full)).1
      (Randomness.SourceProduct.sourceEquiv.symm (ambient, full)).2 =
    (choose adversary parameter auxiliary
      (ConditionalDisclosure.CurveSource.sourceTable (embedScalar scalar) ambient.mask.value
        (ConditionalDisclosure.CurveSource.decode full)) ambient.oracles).bind fun choice =>
      flagObserve adversary parameter auxiliary (decide (¬ ConditionalDisclosure.CurveSource.Complete full.1))
        (choice.1, ambient.oracles, ambient.inputKey, choice.2)
        (curveMaskSampleGarble (embedScalar scalar) ambient.mask.value choice.1
          (ConditionalDisclosure.CurveSource.decode full)).request := by
  unfold seedKernel tableOf requestOf
  rw [restored_source]
  rfl

/-- The full virtual source is exactly independent real used seeds and complete
raw tags. This is a virtual programmed experiment, not an iid claim about real queried tags. -/
theorem fullFlagged_seed {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (scalar : ScalarField) (auxiliary : Aux) :
    fullFlagged adversary parameter scalar auxiliary =
      (PMF.uniformOfFintype Randomness.Seed).bind fun seed =>
        (PMF.uniformOfFintype FullTag).bind (seedKernel adversary parameter scalar auxiliary seed) := by
  rw [Randomness.SourceProduct.independent_bind, Simulation.CoinProduct.ambient_uniform_bind]
  simp only [restored_kernel]
  unfold fullFlagged fullContinue chooseGlobal
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  apply congrArg ((PMF.uniformOfFintype NonZeroBase).bind)
  funext mask
  rw [PMF.bind_comm (PMF.uniformOfFintype Randomness.SourceProduct.TagSource)
    (PMF.uniformOfFintype SimulatorOracleCoin)]
  apply congrArg ((PMF.uniformOfFintype SimulatorOracleCoin).bind)
  funext oracles
  rw [PMF.bind_comm (PMF.uniformOfFintype Randomness.SourceProduct.TagSource)
    (PMF.uniformOfFintype InputMacKey)]

/-- Only the checked unused tape factor is integrated out here. -/
theorem fullFlagged_tape {Aux : Type}
    (witness : Garbling.Randomness)
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (scalar : ScalarField) (auxiliary : Aux) :
    fullFlagged adversary parameter scalar auxiliary =
      (randomTape witness parameter).bind fun tape =>
        (PMF.uniformOfFintype FullTag).bind (seedKernel adversary parameter scalar auxiliary (Randomness.tapeSeed tape)) := by
  rw [fullFlagged_seed]
  exact (Randomness.tapeSeed_bind witness parameter (fun seed =>
    (PMF.uniformOfFintype FullTag).bind (seedKernel adversary parameter scalar auxiliary seed))).symm

/-- The internal flag is computed before the second adversary phase; its public
label argument is unchanged. -/
def sourceEncode (scalar : ScalarField) (source : TapeSource) (state : SimulatorState) (input : AffineInput) :
    (Garbling.Labels × Bool) × SimulatorState :=
  let seed := Randomness.tapeSeed source.1
  let request := requestOf scalar seed source.2 input
  let labels : Garbling.Labels := ⟨BitInput.ofAffine input, seed.inputKey.encodeAffine input⟩
  let bad := decide (¬ ConditionalDisclosure.CurveSource.Complete source.2.1) ||
    decide (LabelCollision.GridCollision state.fixedTranscript (LabelCollision.selectedUses request input) seed.inputKey)
  ((labels, bad), programGateSchedule state (request.schedule input labels.inputMac))

def virtualTranscript {Aux : Type}
    (witness : Garbling.Randomness)
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (scalar : ScalarField) (auxiliary : Aux) : PMF (Transcript adversary.State × Bool) :=
  FlaggedMass.flaggedTranscript idealOracleHandler
    ((randomTape witness parameter).bind fun tape => (PMF.uniformOfFintype FullTag).map (Prod.mk tape))
    (fun source => tableOf scalar (Randomness.tapeSeed source.1) source.2)
    (fun source => initial (Randomness.tapeSeed source.1).oracles)
    (fun table => adversary.chooseInput parameter table auxiliary)
    (fun source state selected => sourceEncode scalar source state selected.1)
    (fun table selected labels => adversary.decide parameter table labels auxiliary selected.2)

/-- The virtual full source has the standard flagged two-phase mass factorization. -/
theorem fullFlagged_virtual {Aux : Type}
    (witness : Garbling.Randomness)
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (scalar : ScalarField) (auxiliary : Aux) :
    fullFlagged adversary parameter scalar auxiliary =
      virtualTranscript witness adversary parameter scalar auxiliary := by
  rw [fullFlagged_tape]
  unfold virtualTranscript FlaggedMass.flaggedTranscript sampledTwoPhaseTranscript
  simp only [PMF.bind_bind, PMF.bind_map, PMF.map_bind]
  apply congrArg ((randomTape witness parameter).bind)
  funext tape
  apply congrArg ((PMF.uniformOfFintype FullTag).bind)
  funext tag
  unfold seedKernel choose flagObserve observe twoPhaseTranscript sourceEncode
  simp only [PMF.bind_map, PMF.pure_bind, PMF.map_bind, PMF.map_comp,
    Function.comp_def, localChoice, FlaggedMass.transcriptEquiv, Equiv.coe_fn_mk, Prod.mk.eta]

end
end Kriterion.DirectDisclosure.SourceKernel
