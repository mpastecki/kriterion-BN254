import Construction.TruncatedBiquadratic
import Proof.TruncatedBitAdaptor

namespace Kriterion.ArgoMAC.TruncatedBiquadratic

open BN254 Cryptography

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

private theorem projectDigit_get (rows : Vector BitAdaptor.Table coordinateBitCount)
    (index : Fin coordinateBitCount) :
    (projectRows rows).get index =
      ⟨TruncatedBitAdaptor.truncate (rows.get index).trueRow⟩ := by
  simp only [projectRows, Vector.get_ofFn]

theorem evaluateDigit_projected_garble (permutations : Nat → BitAdaptor.FixedKeyPermutations)
    (slope : BaseField) (key : CoordinateMacKey) (value : BaseField) :
    evaluateDigit permutations
      (projectDigit (some (DigitAdaptor.garble
        (fun position => BitAdaptor.fixedKeyOracle (permutations position)) slope key).1))
      value (encodeCoordinate key (coordinateBits value)) =
      slope * value + DigitAdaptor.bitsK
        (DigitAdaptor.garble
          (fun position => BitAdaptor.fixedKeyOracle (permutations position)) slope key).2 := by
  change evaluateDigit permutations
    (some (projectRows (DigitAdaptor.garble
      (fun position => BitAdaptor.fixedKeyOracle (permutations position)) slope key).1))
    value (encodeCoordinate key (coordinateBits value)) = _
  unfold evaluateDigit
  rw [show encodeCoordinate key (coordinateBits value) =
    DigitAdaptor.encode key (coordinateValues value) from rfl]
  have pointwise : (fun index : Fin coordinateBitCount =>
      TruncatedBitAdaptor.evaluate (permutations index.val)
        ((projectRows (DigitAdaptor.garble
          (fun position => BitAdaptor.fixedKeyOracle (permutations position)) slope key).1).get index)
        (coordinateValues value index)
        ((DigitAdaptor.encode key (coordinateValues value)).get index)) =
      (fun index : Fin coordinateBitCount => (DigitAdaptor.selectedOutputs
        (DigitAdaptor.garble
          (fun position => BitAdaptor.fixedKeyOracle (permutations position)) slope key).2
        (coordinateValues value)).get index) := by
    funext index
    rw [projectDigit_get, digit_garble_table_get, digit_encode_get,
      digit_selected_get, digit_garble_output_get]
    exact TruncatedBitAdaptor.evaluate_projected_garble
      (permutations index.val) slope (key.get index) (coordinateValues value index)
  calc
    _ = DigitAdaptor.fromBits (fun index => (DigitAdaptor.selectedOutputs
        (DigitAdaptor.garble
          (fun position => BitAdaptor.fixedKeyOracle (permutations position)) slope key).2
        (coordinateValues value)).get index) :=
      congrArg (DigitAdaptor.fromBits (count := coordinateBitCount)) pointwise
    _ = _ := by
      rw [DigitAdaptor.fromBitsSelectedOutputs slope _
        (DigitAdaptor.garbleSlope _ slope key), coordinateBitValue]

private theorem evaluateDigit_pipeline_garble
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (location : Pipeline.FixedKeyLocation)
    (slope : BaseField) (key : CoordinateMacKey) (value : BaseField) :
    evaluateDigit (fun position => Pipeline.fixedKeyPermutations oracle location position)
      (projectDigit (some (DigitAdaptor.garble
        (Pipeline.fixedKeyGate oracle location) slope key).1))
      value (encodeCoordinate key (coordinateBits value)) =
      slope * value + DigitAdaptor.bitsK
        (DigitAdaptor.garble (Pipeline.fixedKeyGate oracle location) slope key).2 := by
  exact evaluateDigit_projected_garble
    (fun position => Pipeline.fixedKeyPermutations oracle location position) slope key value

theorem evaluateX_projected_garble
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (output : Fin FieldMacToECMac.outputMacCount) (coordinate : Pipeline.PointCoordinate)
    (c0 c1 c2 c3 c5 : BaseField) (randomness : Biquadratic.XRandomness)
    (key : InputMacKey) (input : AffineInput) :
    evaluate (pointOracles oracle output coordinate)
      (project (Biquadratic.garbleX c0 c1 c2 c3 c5 randomness
        (Pipeline.biquadraticOracles oracle output coordinate) key)) input
      (key.encodeAffine input) =
      c0 + c1 * input.x + c2 * input.y + c3 * input.x * input.y + c5 * input.y ^ 2 := by
  simp only [evaluate, project, Biquadratic.garbleX, pointOracles,
    Pipeline.biquadraticOracles, InputMacKey.encodeAffine,
    InputMacKey.encode, BitInput.ofAffine, coefficient, Option.getD_some, Option.getD_none]
  rw [evaluateDigit_pipeline_garble, evaluateDigit_pipeline_garble,
    evaluateDigit_pipeline_garble, evaluateDigit_pipeline_garble]
  simp only [projectDigit, Option.map_none, evaluateDigit]
  ring

theorem evaluateY_projected_garble
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (output : Fin FieldMacToECMac.outputMacCount) (coordinate : Pipeline.PointCoordinate)
    (c0 c1 c4 c5 : BaseField) (randomness : Biquadratic.YRandomness)
    (key : InputMacKey) (input : AffineInput) :
    evaluateY (pointOracles oracle output coordinate)
      (project (Biquadratic.garbleY c0 c1 c4 c5 randomness
        (Pipeline.biquadraticOracles oracle output coordinate) key)) input
      (key.encodeAffine input) =
      c0 + 3 * c5 + c1 * input.x + c4 * input.x ^ 2 + c5 * input.x ^ 3 := by
  simp only [evaluateY, project, Biquadratic.garbleY, pointOracles,
    Pipeline.biquadraticOracles, InputMacKey.encodeAffine,
    InputMacKey.encode, BitInput.ofAffine, coefficient, Option.getD_some]
  rw [evaluateDigit_pipeline_garble, evaluateDigit_pipeline_garble,
    evaluateDigit_pipeline_garble]
  ring

theorem evaluateZ_projected_garble
    (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (output : Fin FieldMacToECMac.outputMacCount) (coordinate : Pipeline.PointCoordinate)
    (c0 c2 c3 c4 c5 : BaseField) (randomness : Biquadratic.ZRandomness)
    (key : InputMacKey) (input : AffineInput) :
    evaluate (pointOracles oracle output coordinate)
      (project (Biquadratic.garbleZ c0 c2 c3 c4 c5 randomness
        (Pipeline.biquadraticOracles oracle output coordinate) key)) input
      (key.encodeAffine input) =
      c0 + c2 * input.y + c3 * input.x * input.y + c4 * input.x ^ 2 + c5 * input.y ^ 2 := by
  simp only [evaluate, project, Biquadratic.garbleZ, pointOracles,
    Pipeline.biquadraticOracles, InputMacKey.encodeAffine,
    InputMacKey.encode, BitInput.ofAffine, coefficient, Option.getD_some, Option.getD_none]
  rw [evaluateDigit_pipeline_garble, evaluateDigit_pipeline_garble,
    evaluateDigit_pipeline_garble, evaluateDigit_pipeline_garble,
    evaluateDigit_pipeline_garble]
  ring

end Kriterion.ArgoMAC.TruncatedBiquadratic
