import Construction.Garbling

namespace Kriterion.ConditionalDisclosure

open BN254 Cryptography ArgoMAC

abbrev Ciphertext := BitVec 256

structure Public where
  curve : CurveMembership.Table
  scalarCiphertext : Ciphertext

def pad (oracle : EncPRF.HashOracle) (bridge : BaseField) : Ciphertext :=
  (oracle bridge).2 ++ (oracle bridge).1

def scalarBytes (scalar : ScalarField) : Ciphertext := BitVec.ofNat 256 scalar.val

def encrypt (oracle : EncPRF.HashOracle) (bridge : BaseField)
    (scalar : ScalarField) : Ciphertext := pad oracle bridge ^^^ scalarBytes scalar

def decrypt (oracle : EncPRF.HashOracle) (bridge : BaseField)
    (ciphertext : Ciphertext) : ScalarField := (pad oracle bridge ^^^ ciphertext).toNat

theorem decrypt_encrypt (oracle : EncPRF.HashOracle) (bridge : BaseField)
    (scalar : ScalarField) : decrypt oracle bridge (encrypt oracle bridge scalar) = scalar := by
  unfold decrypt encrypt
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  simp only [scalarBytes, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt]
  · exact ZMod.natCast_zmod_val scalar
  · exact lt_trans scalar.val_lt (by decide)

def garble (scalar : ScalarField) (tape : Garbling.Randomness) : Public := {
  curve := CurveMembership.garble tape.bridgeKey tape.curveMask.value tape.curveR1 tape.curveR2
    (Pipeline.curveOracles tape.fixedKeyOracle) tape.inputMacKey
  scalarCiphertext := encrypt tape.hashOracle tape.bridgeKey scalar
}

def evaluate [FieldCertificate] [GroupCertificate]
    (oracle : Garbling.EvaluationOracle) (table : Public) (input : AffineInput)
    (labels : InputMac) : Option Point :=
  match decodePoint input with
  | none => none
  | some point =>
    let bridge := CurveMembership.evaluate (Pipeline.curveOracles oracle.1)
      table.curve input labels
    some (scalarMultiplication (decrypt oracle.2.2 bridge table.scalarCiphertext) point)

theorem evaluate_garble [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (tape : Garbling.Randomness) (input : AffineInput) :
    evaluate (tape.fixedKeyOracle, tape.encPRFOracle, tape.hashOracle)
      (garble scalar tape) input (tape.inputMacKey.encodeAffine input) =
      checkedScalarMultiplication scalar input := by
  unfold evaluate checkedScalarMultiplication
  cases decoded : decodePoint input with
  | none => rfl
  | some point =>
    have valid : OnCurve input := (decodePoint_defined input).mp (by simp [decoded])
    simp only [garble]
    rw [CurveMembership.evaluateEncodedOnCurve _ _ _ _ _ _ _ valid, decrypt_encrypt]
    rfl

end Kriterion.ConditionalDisclosure
