import Construction.TruncatedCurveMembership
import Proof.TruncatedBitAdaptor

namespace Kriterion.ArgoMAC.TruncatedCurveMembership

open BN254 Cryptography

theorem projectRow_get (rows : Vector BitAdaptor.Table coordinateBitCount)
    (index : Fin coordinateBitCount) :
    (projectRow rows).get index = ⟨TruncatedBitAdaptor.truncate (rows.get index).trueRow⟩ := by
  simp only [projectRow, Vector.get_ofFn]

private theorem digit_garble_table_get {count : Nat}
    (windows : Nat → BitAdaptor.FixedKeyOracle) (slope : BaseField)
    (key : Vector BitAdaptor.Key count) (index : Fin count) :
    ((DigitAdaptor.garble windows slope key).1).get index =
      (BitAdaptor.garble (windows index.val) slope (key.get index)).1 := by
  simp only [DigitAdaptor.garble, Vector.get_map, Vector.get_ofFn]

private theorem digit_garble_output_get {count : Nat}
    (windows : Nat → BitAdaptor.FixedKeyOracle) (slope : BaseField)
    (key : Vector BitAdaptor.Key count) (index : Fin count) :
    ((DigitAdaptor.garble windows slope key).2).get index =
      (BitAdaptor.garble (windows index.val) slope (key.get index)).2 := by
  simp only [DigitAdaptor.garble, Vector.get_map, Vector.get_ofFn]

private theorem digit_encode_get {count : Nat} (key : Vector BitAdaptor.Key count)
    (values : Fin count → Bool) (index : Fin count) :
    (DigitAdaptor.encode key values).get index = BitAdaptor.encode (key.get index) (values index) := by
  simp only [DigitAdaptor.encode, Vector.get_ofFn]

private theorem digit_selected_get {count : Nat} (key : Vector BitAdaptor.OutputKey count)
    (values : Fin count → Bool) (index : Fin count) :
    (DigitAdaptor.selectedOutputs key values).get index = (key.get index).encode (values index) := by
  simp only [DigitAdaptor.selectedOutputs, Vector.get_ofFn]

theorem evaluateDigit_projected_garble
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block) (kind : Pipeline.CurveAdaptor)
    (slope : BaseField) (key : CoordinateMacKey) (value : BaseField) :
    evaluateDigit (curvePermutations oracle kind)
      (projectRow (DigitAdaptor.garble
        (fun position => Pipeline.fixedKeyGate oracle (.curve kind) position) slope key).1)
      value (encodeCoordinate key (coordinateBits value)) =
      slope * value + DigitAdaptor.bitsK
        (DigitAdaptor.garble
          (fun position => Pipeline.fixedKeyGate oracle (.curve kind) position) slope key).2 := by
  unfold evaluateDigit
  rw [show encodeCoordinate key (coordinateBits value) =
    DigitAdaptor.encode key (coordinateValues value) from rfl]
  have pointwise : (fun index : Fin coordinateBitCount =>
      TruncatedBitAdaptor.evaluate (curvePermutations oracle kind index.val)
        ((projectRow (DigitAdaptor.garble
          (fun position => Pipeline.fixedKeyGate oracle (.curve kind) position) slope key).1).get index)
        (coordinateValues value index)
        ((DigitAdaptor.encode key (coordinateValues value)).get index)) =
      (fun index : Fin coordinateBitCount => (DigitAdaptor.selectedOutputs
        (DigitAdaptor.garble
          (fun position => Pipeline.fixedKeyGate oracle (.curve kind) position) slope key).2
        (coordinateValues value)).get index) := by
    funext index
    rw [projectRow_get, digit_garble_table_get, digit_encode_get,
      digit_selected_get, digit_garble_output_get]
    exact TruncatedBitAdaptor.evaluate_projected_garble
      (curvePermutations oracle kind index.val) slope (key.get index) (coordinateValues value index)
  calc
    _ = DigitAdaptor.fromBits (fun index => (DigitAdaptor.selectedOutputs
        (DigitAdaptor.garble
          (fun position => Pipeline.fixedKeyGate oracle (.curve kind) position) slope key).2
        (coordinateValues value)).get index) :=
      congrArg (DigitAdaptor.fromBits (count := coordinateBitCount)) pointwise
    _ = _ := by
      rw [DigitAdaptor.fromBitsSelectedOutputs slope _
        (DigitAdaptor.garbleSlope _ slope key), coordinateBitValue]

/-- All five projected row families preserve the exact membership polynomial. -/
theorem evaluate_projected_garble
    (bridgeKey mask r1 r2 : BaseField)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (inputKey : InputMacKey) (input : AffineInput) :
    evaluate oracle
      (project (CurveMembership.garble bridgeKey mask r1 r2 (Pipeline.curveOracles oracle) inputKey))
      input (inputKey.encodeAffine input) =
      bridgeKey + mask * (input.x ^ 3 + 3 - input.y ^ 2) := by
  simp only [evaluate, project, CurveMembership.garble, Pipeline.curveOracles,
    InputMacKey.encodeAffine, InputMacKey.encode, BitInput.ofAffine]
  rw [evaluateDigit_projected_garble, evaluateDigit_projected_garble,
    evaluateDigit_projected_garble, evaluateDigit_projected_garble,
    evaluateDigit_projected_garble]
  ring

/-- On-curve inputs release exactly the original bridge key after row truncation. -/
theorem evaluate_projected_garble_onCurve
    (bridgeKey mask r1 r2 : BaseField)
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (inputKey : InputMacKey) (input : AffineInput) (onCurve : OnCurve input) :
    evaluate oracle
      (project (CurveMembership.garble bridgeKey mask r1 r2 (Pipeline.curveOracles oracle) inputKey))
      input (inputKey.encodeAffine input) = bridgeKey := by
  rw [evaluate_projected_garble]
  rw [show input.x ^ 3 + 3 - input.y ^ 2 = 0 by rw [onCurve]; ring]
  ring

end Kriterion.ArgoMAC.TruncatedCurveMembership
