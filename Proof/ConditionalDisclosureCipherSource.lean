import Proof.ConditionalDisclosurePadBridge
import Proof.Privacy.Source.HiddenHashSource

namespace Kriterion.ConditionalDisclosure.CipherSource

open BN254 Cryptography ArgoMAC ArgoMAC.Security
open scoped ENNReal
noncomputable section

attribute [local instance] Classical.propDecidable ciphertextFintype

/-- The source translation uses every bit of the scalar ciphertext. -/
def padCipherEquiv (scalar : ScalarField) : Hash.Pair ≃ Ciphertext :=
  ({ toFun := Hash.translate (scalarMask scalar)
     invFun := Hash.translate (scalarMask scalar)
     left_inv := Hash.translate_twice (scalarMask scalar)
     right_inv := Hash.translate_twice (scalarMask scalar) } : Hash.Pair ≃ Hash.Pair).trans pairEquiv

theorem padCipherEquiv_apply (scalar : ScalarField) (oracle : EncPRF.HashOracle)
    (bridge : BaseField) :
    padCipherEquiv scalar (oracle bridge) = encrypt oracle bridge scalar :=
  encryption_pair oracle bridge scalar

/-- On a missed hash input, the real ciphertext may be replaced by a fully independent
uniform256-bit ciphertext inside any exact full-transcript source weight. The miss
condition must later be bounded after the actual adaptive bridge/source transport. -/
theorem hidden_ciphertext_weighted_eq [Fintype Block] [Fintype BaseField]
    (bridge : BaseField) (randomness : Garbling.Randomness)
    (transcript : List (Sigma Garbling.oracleSpec.Answer))
    (miss : bridge ∉ transcriptHashInputs transcript)
    (scalar : ScalarField) (weight : Ciphertext → ℝ≥0∞) :
    (∑' oracle : EncPRF.HashOracle,
      (PMF.uniformOfFintype EncPRF.HashOracle) oracle *
        (if OracleTranscriptCompatible Garbling.oracleHandler
            {randomness with hashOracle := oracle} transcript then
          weight (encrypt oracle bridge scalar) else 0)) =
    ∑' sample : EncPRF.HashOracle × Ciphertext,
      (PMF.uniformOfFintype (EncPRF.HashOracle × Ciphertext)) sample *
        (if OracleTranscriptCompatible Garbling.oracleHandler
            {randomness with hashOracle := sample.1} transcript then weight sample.2 else 0) := by
  have split := hiddenHashTranscript_weighted_eq bridge randomness transcript miss
    (fun pair => weight (padCipherEquiv scalar pair))
  simp only [padCipherEquiv_apply] at split
  let equivalence : (EncPRF.HashOracle × Hash.Pair) ≃ (EncPRF.HashOracle × Ciphertext) :=
    (Equiv.refl _).prodCongr (padCipherEquiv scalar)
  let observe : EncPRF.HashOracle × Ciphertext → ℝ≥0∞ := fun sample =>
    if OracleTranscriptCompatible Garbling.oracleHandler
      {randomness with hashOracle := sample.1} transcript then weight sample.2 else 0
  have transported := pmf_map_weighted_sum
    (PMF.uniformOfFintype (EncPRF.HashOracle × Hash.Pair)) equivalence observe
  rw [map_uniformOfFintype_equivBetween] at transported
  exact split.trans transported.symm

end
end Kriterion.ConditionalDisclosure.CipherSource
