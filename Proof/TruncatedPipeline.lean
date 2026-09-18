import Construction.TruncatedPipeline
import Proof.TruncatedBiquadratic
import Proof.TruncatedCurveMembership

namespace Kriterion.ArgoMAC.TruncatedFieldMacToECMac
open BN254 Cryptography

theorem evaluateHomogeneous_projected_garble
    (rows : FieldMacToECMac.Rows) (randomness : FieldMacToECMac.Randomness)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (key : InputMacKey) (input : AffineInput)
    (sparse : ∀ index, FieldMacToECMac.SparseRow (rows.get index)) :
    evaluateHomogeneous
      (project (FieldMacToECMac.garble rows randomness (Pipeline.pointOracles oracle) key))
      (pointOracles oracle) input (key.encodeAffine input) =
      FieldMacToECMac.representedRows rows input := by
  apply Vector.ext
  intro index inRange
  have rowSparse := sparse ⟨index, inRange⟩
  rcases rowSparse with ⟨xX2, yY, yXY, zX⟩
  simp only [evaluateHomogeneous, project, pointOracles, FieldMacToECMac.garble,
    FieldMacToECMac.garbleRow, Pipeline.pointOracles,
    Vector.getElem_ofFn, Vector.get_map, Vector.get_ofFn]
  rw [TruncatedBiquadratic.evaluateX_projected_garble,
    TruncatedBiquadratic.evaluateY_projected_garble,
    TruncatedBiquadratic.evaluateZ_projected_garble]
  simp [FieldMacToECMac.representedRows, FieldMacToECMac.representedRow,
    Coordinates.evaluate, xX2, zX]
  ring_nf
  constructor <;> trivial

theorem evaluate_projected_garble
    (rows : FieldMacToECMac.Rows) (randomness : FieldMacToECMac.Randomness)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (key : InputMacKey) (input : AffineInput)
    (sparse : ∀ index, FieldMacToECMac.SparseRow (rows.get index)) :
    evaluate
      (project (FieldMacToECMac.garble rows randomness (Pipeline.pointOracles oracle) key))
      (pointOracles oracle) input (key.encodeAffine input) =
      FieldMacToECMac.representedResult rows input := by
  rw [evaluate, evaluateHomogeneous_projected_garble rows randomness oracle key input sparse]
  rfl

end Kriterion.ArgoMAC.TruncatedFieldMacToECMac

namespace Kriterion.ArgoMAC.TruncatedPipeline
open BN254 Cryptography

theorem evaluateEncoded [FieldCertificate]
    (outputKeys : FieldMacToECMac.OutputKeys)
    (pointRandomness : FieldMacToECMac.Randomness)
    (bridgeKey : BaseField) (curveMask : NonZeroBase) (curveR1 curveR2 : BaseField)
    (fixedKeyOracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (encPRFOracle : PermutationOracle EncPRF.PermutationIndex Block)
    (hashOracle : EncPRF.HashOracle) (inputKey : InputMacKey)
    (input : AffineInput) (point : Point) (decoded : decodePoint input = some point) :
    evaluate fixedKeyOracle encPRFOracle hashOracle
      (project (Pipeline.garble outputKeys pointRandomness bridgeKey curveMask
        curveR1 curveR2 fixedKeyOracle encPRFOracle hashOracle inputKey))
      (BitInput.ofAffine input) (inputKey.encode (BitInput.ofAffine input)) =
      some (FieldMacToECMac.expectedResult
        (FieldMacToECMac.rowsForOutputKeys outputKeys pointRandomness) input) := by
  have onCurve : OnCurve input := (decodePoint_defined input).mp (by simp [decoded])
  simp only [evaluate, BitInput.toAffineOfAffine, decoded, project, Pipeline.garble]
  rw [InputMacKey.encodeOfAffine,
    TruncatedCurveMembership.evaluate_projected_garble_onCurve _ _ _ _ _ _ _ onCurve]
  rw [← InputMacKey.encodeOfAffine inputKey input, EncPRF.transformEncode,
    InputMacKey.encodeOfAffine]
  rw [TruncatedFieldMacToECMac.evaluate_projected_garble _ _ _ _ _
    (FieldMacToECMac.rowsForOutputKeysSparse outputKeys pointRandomness)]
  rw [FieldMacToECMac.representedResult_onCurve _ input
    (FieldMacToECMac.rowsForOutputKeysSparse outputKeys pointRandomness) onCurve]

theorem evaluate_projected_garble [FieldCertificate]
    (outputKeys : FieldMacToECMac.OutputKeys)
    (pointRandomness : FieldMacToECMac.Randomness)
    (bridgeKey : BaseField) (curveMask : NonZeroBase) (curveR1 curveR2 : BaseField)
    (fixedKeyOracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (encPRFOracle : PermutationOracle EncPRF.PermutationIndex Block)
    (hashOracle : EncPRF.HashOracle) (inputKey : InputMacKey) (input : AffineInput) :
    evaluate fixedKeyOracle encPRFOracle hashOracle
      (project (Pipeline.garble outputKeys pointRandomness bridgeKey curveMask
        curveR1 curveR2 fixedKeyOracle encPRFOracle hashOracle inputKey))
      (BitInput.ofAffine input) (inputKey.encodeAffine input) =
    Pipeline.evaluate fixedKeyOracle encPRFOracle hashOracle
      (Pipeline.garble outputKeys pointRandomness bridgeKey curveMask
        curveR1 curveR2 fixedKeyOracle encPRFOracle hashOracle inputKey)
      (BitInput.ofAffine input) (inputKey.encodeAffine input) := by
  cases decoded : decodePoint input with
  | none => simp [evaluate, Pipeline.evaluate, BitInput.toAffineOfAffine, decoded]
  | some point =>
    exact (evaluateEncoded outputKeys pointRandomness bridgeKey curveMask curveR1 curveR2
      fixedKeyOracle encPRFOracle hashOracle inputKey input point decoded).trans
      (Pipeline.evaluateEncoded outputKeys pointRandomness bridgeKey curveMask curveR1 curveR2
        fixedKeyOracle encPRFOracle hashOracle inputKey input point decoded).symm

end Kriterion.ArgoMAC.TruncatedPipeline
