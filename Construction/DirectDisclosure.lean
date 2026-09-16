import Construction.Garbling

namespace Kriterion.DirectDisclosure

open BN254 Cryptography ArgoMAC

abbrev Public := CurveMembership.Table

def embedScalar (scalar : ScalarField) : BaseField := scalar.val

def decodeScalar (value : BaseField) : ScalarField := value.val

theorem scalarModulus_lt_base : scalarFieldModulus < baseFieldModulus := by decide

theorem decode_embed (scalar : ScalarField) : decodeScalar (embedScalar scalar) = scalar := by
  simp only [decodeScalar, embedScalar, ZMod.val_natCast]
  rw [Nat.mod_eq_of_lt (lt_trans scalar.val_lt scalarModulus_lt_base)]
  exact ZMod.natCast_zmod_val scalar

/-- The curve table conditionally discloses the scalar itself. -/
def garble (scalar : ScalarField) (tape : Garbling.Randomness) : Public :=
  CurveMembership.garble (embedScalar scalar) tape.curveMask.value tape.curveR1 tape.curveR2
    (Pipeline.curveOracles tape.fixedKeyOracle) tape.inputMacKey

def evaluate [FieldCertificate] [GroupCertificate]
    (oracle : Garbling.EvaluationOracle) (table : Public) (input : AffineInput)
    (labels : InputMac) : Option Point :=
  (decodePoint input).map fun point =>
    scalarMultiplication (decodeScalar
      (CurveMembership.evaluate (Pipeline.curveOracles oracle.1) table input labels)) point

theorem evaluate_garble [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField) (tape : Garbling.Randomness) (input : AffineInput) :
    evaluate (tape.fixedKeyOracle, tape.encPRFOracle, tape.hashOracle)
      (garble scalar tape) input (tape.inputMacKey.encodeAffine input) =
      checkedScalarMultiplication scalar input := by
  unfold evaluate checkedScalarMultiplication
  cases decoded : decodePoint input with
  | none => simp only [Option.map_none]
  | some point =>
    have valid : OnCurve input := (decodePoint_defined input).mp (by simp [decoded])
    simp only [garble, Option.map_some]
    rw [CurveMembership.evaluateEncodedOnCurve _ _ _ _ _ _ _ valid, decode_embed]

end Kriterion.DirectDisclosure
