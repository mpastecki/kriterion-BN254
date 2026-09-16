import Construction.ConditionalDisclosureScheme
import Proof.ConditionalDisclosureRandomness
import Security.AdaptivePrivacy

namespace Kriterion.ConditionalDisclosure.Randomness

open BN254 Cryptography ArgoMAC ArgoMAC.Security
noncomputable section

/-- The projected real handler exposes the unchanged three-oracle public interface. -/
def handler : OracleHandler Garbling.oracleSpec CurveRandomness :=
  publicHandler fun sample =>
    (sample.2.fixedKeyOracle, sample.2.encPRFOracle, sample.2.hashOracle)

private theorem handlers_agree (query : Garbling.OracleQuery) (tape : Garbling.Randomness) :
    (Garbling.oracleHandler query tape).1 = (handler query (project tape)).1 ∧
      project (Garbling.oracleHandler query tape).2 = (handler query (project tape)).2 := by
  cases query <;> exact ⟨rfl, rfl⟩

/-- Projection preserves every query and private sample in either adversary phase. -/
theorem run_project {Result : Type*} {budget : Nat}
    (program : OracleProgram Garbling.oracleSpec Result budget) (tape : Garbling.Randomness) :
    (program.run Garbling.oracleHandler tape).map (fun result => (result.1, project result.2)) =
      program.run handler (project tape) :=
  OracleProgram.run_project Garbling.oracleHandler handler project handlers_agree program tape

private theorem run_result {Result : Type*} {budget : Nat}
    (program : OracleProgram Garbling.oracleSpec Result budget) (tape : Garbling.Randomness) :
    (program.run Garbling.oracleHandler tape).map Prod.fst =
      (program.run handler (project tape)).map Prod.fst := by
  have same := congrArg (fun distribution => distribution.map Prod.fst) (run_project program tape)
  simpa only [PMF.map_comp, Function.comp_def] using same

def labels (sample : CurveRandomness) (input : AffineInput) : Garbling.Labels :=
  ⟨BitInput.ofAffine input, sample.2.inputMacKey.encodeAffine input⟩

/-- This kernel uses the exact real garbler and selected labels, with unused point
randomness removed and all adversary query behavior retained. -/
def realKernel {Aux : Type*}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux)
    (sample : CurveRandomness) : PMF Bool :=
  let table := garbleProjected scalar.value sample
  ((adversary.chooseInput parameter table auxiliary).run handler sample).bind fun selected =>
    ((adversary.decide parameter table (labels sample selected.1.1)
      auxiliary selected.1.2).run handler selected.2).map Prod.fst

private theorem realKernel_project {Aux : Type*}
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) (tape : Garbling.Randomness) :
    ((adversary.chooseInput parameter (garble scalar.value tape) auxiliary).run
      Garbling.oracleHandler tape).bind (fun selected =>
        ((adversary.decide parameter (garble scalar.value tape)
          (⟨BitInput.ofAffine selected.1.1, tape.inputMacKey.encodeAffine selected.1.1⟩ : Garbling.Labels)
          auxiliary selected.1.2).run Garbling.oracleHandler selected.2).map Prod.fst) =
      realKernel adversary parameter scalar auxiliary (project tape) := by
  simp_rw [run_result]
  rw [realKernel, ← run_project, PMF.bind_map]
  rfl

/-- This is the actual two-stage real game, not merely the garbler's marginal.
The first phase sees both public components before adaptively selecting its input. -/
theorem realGame_project [FieldCertificate] [GroupCertificate] {Aux : Type*}
    (witness : Garbling.Randomness)
    (adversary : GarbledCircuit.AdaptiveAdversary Garbling.oracleSpec AffineInput Public Garbling.Labels Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) :
    letI : Nonempty CurveRandomness := ⟨project witness⟩
    GarbledCircuit.realGame internalScheme (randomTape witness) Garbling.oracleHandler
      adversary parameter scalar auxiliary =
      (PMF.uniformOfFintype CurveRandomness).bind (realKernel adversary parameter scalar auxiliary) := by
  letI : Nonempty CurveRandomness := ⟨project witness⟩
  change (randomTape witness parameter).bind (fun tape => _) = _
  have phases : (randomTape witness parameter).bind (fun tape =>
      ((adversary.chooseInput parameter (garble scalar.value tape) auxiliary).run
        Garbling.oracleHandler tape).bind (fun selected =>
          ((adversary.decide parameter (garble scalar.value tape)
            (⟨BitInput.ofAffine selected.1.1, tape.inputMacKey.encodeAffine selected.1.1⟩ : Garbling.Labels)
            auxiliary selected.1.2).run Garbling.oracleHandler selected.2).map Prod.fst)) =
      (randomTape witness parameter).bind (realKernel adversary parameter scalar auxiliary ∘ project) := by
    apply congrArg ((randomTape witness parameter).bind)
    funext tape
    exact realKernel_project adversary parameter scalar auxiliary tape
  dsimp only [internalScheme]
  rw [phases, ← PMF.bind_map, project_uniform]

end
end Kriterion.ConditionalDisclosure.Randomness
