import Construction.ConditionalDisclosure
import Proof.ConditionalDisclosurePad

namespace Kriterion.ConditionalDisclosure

open BN254 ArgoMAC

/-- Hash pairs are stored low block first. -/
def joinPair (value : Hash.Pair) : Ciphertext := value.2 ++ value.1

def splitPair (value : Ciphertext) : Hash.Pair :=
  (value.extractLsb' 0 128, value.extractLsb' 128 128)

theorem join_split (value : Ciphertext) : joinPair (splitPair value) = value := by
  simp only [joinPair, splitPair]
  rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide : 128 = 0 + 128)]
  simp

theorem split_join (value : Hash.Pair) : splitPair (joinPair value) = value := by
  apply Prod.ext
  · simp only [splitPair, joinPair]
    rw [BitVec.extractLsb'_append_eq_of_add_le (by decide)]
    simp
  · simp only [splitPair, joinPair]
    rw [BitVec.extractLsb'_append_eq_of_le (by decide)]
    simp

def pairEquiv : Hash.Pair ≃ Ciphertext where
  toFun := joinPair
  invFun := splitPair
  left_inv := split_join
  right_inv := join_split

def scalarMask (scalar : ScalarField) : Hash.Pair := splitPair (scalarBytes scalar)

theorem join_translate (shift value : Hash.Pair) :
    joinPair (Hash.translate shift value) = joinPair shift ^^^ joinPair value := by
  exact (BitVec.xor_append (x₁ := shift.2) (x₂ := value.2)
    (y₁ := shift.1) (y₂ := value.1)).symm

theorem join_scalarMask (scalar : ScalarField) :
    joinPair (scalarMask scalar) = scalarBytes scalar := join_split _

theorem encryption_pair (oracle : EncPRF.HashOracle) (bridge : BaseField)
    (scalar : ScalarField) :
    joinPair (Hash.translate (scalarMask scalar) (oracle bridge)) =
      encrypt oracle bridge scalar := by
  rw [join_translate, join_scalarMask]
  exact BitVec.xor_comm _ _

def programValue (scalar : ScalarField) (ciphertext : Ciphertext) : Hash.Pair :=
  Hash.translate (scalarMask scalar) (splitPair ciphertext)

theorem join_programValue (scalar : ScalarField) (ciphertext : Ciphertext) :
    joinPair (programValue scalar ciphertext) = scalarBytes scalar ^^^ ciphertext := by
  rw [programValue, join_translate, join_scalarMask, join_split]

theorem program_encrypt (oracle : EncPRF.HashOracle) (bridge : BaseField)
    (scalar : ScalarField) (ciphertext : Ciphertext) :
    encrypt (Function.update oracle bridge (programValue scalar ciphertext)) bridge scalar =
      ciphertext := by
  unfold encrypt
  change joinPair ((Function.update oracle bridge (programValue scalar ciphertext)) bridge) ^^^
    scalarBytes scalar = ciphertext
  rw [Function.update_self, join_programValue, BitVec.xor_comm (scalarBytes scalar) ciphertext,
    BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

theorem decrypt_program (oracle : EncPRF.HashOracle) (bridge : BaseField)
    (scalar : ScalarField) (ciphertext : Ciphertext) :
    decrypt (Function.update oracle bridge (programValue scalar ciphertext)) bridge ciphertext =
      scalar := by
  have correct := decrypt_encrypt (Function.update oracle bridge (programValue scalar ciphertext))
    bridge scalar
  rwa [program_encrypt] at correct

/-- The conditional hash coupling uses the construction's exact256-bit public ciphertext. -/
theorem concrete_pad_coupling (prior : List (BaseField × Hash.Pair)) (bridge : BaseField)
    (scalar : ScalarField) (fresh : Hash.Fresh prior bridge)
    [Fintype (Hash.Fiber prior)] [Nonempty (Hash.Fiber prior)] :
    (PMF.uniformOfFintype (Hash.Fiber prior × Hash.Pair)).map
      (fun source => (source.1.1, encrypt source.1.1 bridge scalar)) =
    (PMF.uniformOfFintype (Hash.Fiber prior × Hash.Pair)).map
      (fun source => (Function.update source.1.1 bridge
        (Hash.translate (scalarMask scalar) source.2), joinPair source.2)) := by
  have coupled := congrArg (PMF.map (fun value : EncPRF.HashOracle × Hash.Pair =>
    (value.1, joinPair value.2))) (Hash.pad_coupling prior bridge (scalarMask scalar) fresh)
  simp only [PMF.map_comp, Function.comp_def, Hash.realObservation, Hash.simulatedObservation,
    encryption_pair] at coupled
  exact coupled

end Kriterion.ConditionalDisclosure
