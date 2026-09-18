import Proof.Privacy.Simulator.Arithmetic.PublicCurveWire

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol Security
set_option maxRecDepth 4096

/-- The stored X row emits its complete canonical public table. -/
theorem publicXWire_bits (sample : RowPublicSample) (row : Nat) (ram : Word → Word) (pointer : Word)
    (stored : WordsAt ram pointer (1017 + 9920 * row) (rowSchedule.words sample)) :
    (publicXWire row).flatMap (WireSegment.wire ram pointer) =
      (Wire.biquadratic.encode sample.x.request.table).flatMap (fun byte => bits 8 byte.val) := by
  let base := 1017 + 9920 * row
  have source := row_x_words sample ram pointer base stored
  have coefficient (index : Fin 5) :
      ram (pointer + BitVec.ofNat 256 (base + 9915 + index.val)) =
        BitVec.ofNat 256 (sample.x.coefficients index).val := by
    simpa only [coordinateBitCount, Nat.reduceMul, Nat.reduceAdd, Nat.add_assoc] using
      gateData_coefficient 5 4 _ ram pointer (base + 6867) index source
  have table (gate : Fin 4) (index : Fin coordinateBitCount) :
      ram (pointer + BitVec.ofNat 256 (base + 8899 + 254 * gate.val + index.val)) =
        ((sample.x.tables gate).get index).trueRow := by
    simpa only [coordinateBitCount, Nat.reduceMul, Nat.reduceAdd, Nat.add_assoc] using
      gateData_table 5 4 _ ram pointer (base + 6867) gate index source
  simp only [publicXWire, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    XPublicSample.request, BiquadraticXRequest.table]
  rw [Wire.biquadratic_encode_x]
  simp only [List.flatMap_cons, List.flatMap_append, List.flatMap_nil, List.append_nil]
  rw [wireHeader_bits, wireCoefficient_bits ram pointer (base + 9915) 0 _ (coefficient 0),
    wireCoefficient_bits ram pointer (base + 9915) 1 _ (coefficient 1),
    wireCoefficient_bits ram pointer (base + 9915) 2 _ (coefficient 2),
    wireCoefficient_bits ram pointer (base + 9915) 3 _ (coefficient 3),
    wireCoefficient_bits ram pointer (base + 9915) 4 _ (coefficient 4),
    wireOptionalDigit_bits ram pointer (base + 8899) 3 _ (table 3),
    wireOptionalDigit_bits ram pointer (base + 8899) 0 _ (table 0),
    wireOptionalDigit_bits ram pointer (base + 8899) 1 _ (table 1),
    wireOptionalDigit_bits ram pointer (base + 8899) 2 _ (table 2)]
  simp [List.append_assoc]

/-- The stored Y row emits its complete canonical public table. -/
theorem publicYWire_bits (sample : RowPublicSample) (row : Nat) (ram : Word → Word) (pointer : Word)
    (stored : WordsAt ram pointer (1017 + 9920 * row) (rowSchedule.words sample)) :
    (publicYWire row).flatMap (WireSegment.wire ram pointer) =
      (Wire.biquadratic.encode sample.y.request.table).flatMap (fun byte => bits 8 byte.val) := by
  let base := 1017 + 9920 * row
  have source := row_y_words sample ram pointer base stored
  have coefficient (index : Fin 4) :
      ram (pointer + BitVec.ofNat 256 (base + 6863 + index.val)) =
        BitVec.ofNat 256 (sample.y.coefficients index).val := by
    simpa only [coordinateBitCount, Nat.reduceMul, Nat.reduceAdd, Nat.add_assoc] using
      gateData_coefficient 4 4 _ ram pointer (base + 3815) index source
  have table (gate : Fin 4) (index : Fin coordinateBitCount) :
      ram (pointer + BitVec.ofNat 256 (base + 5847 + 254 * gate.val + index.val)) =
        ((sample.y.tables gate).get index).trueRow := by
    simpa only [coordinateBitCount, Nat.reduceMul, Nat.reduceAdd, Nat.add_assoc] using
      gateData_table 4 4 _ ram pointer (base + 3815) gate index source
  simp only [publicYWire, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    YPublicSample.request, BiquadraticYRequest.table]
  rw [Wire.biquadratic_encode_y]
  simp only [List.flatMap_cons, List.flatMap_append, List.flatMap_nil, List.append_nil]
  rw [wireHeader_bits, wireCoefficient_bits ram pointer (base + 6863) 0 _ (coefficient 0),
    wireCoefficient_bits ram pointer (base + 6863) 1 _ (coefficient 1),
    wireCoefficient_bits ram pointer (base + 6863) 2 _ (coefficient 2),
    wireCoefficient_bits ram pointer (base + 6863) 3 _ (coefficient 3),
    wireOptionalDigit_bits ram pointer (base + 5847) 2 _ (table 2),
    wireOptionalDigit_bits ram pointer (base + 5847) 3 _ (table 3),
    wireOptionalDigit_bits ram pointer (base + 5847) 0 _ (table 0),
    wireOptionalDigit_bits ram pointer (base + 5847) 1 _ (table 1)]
  simp [List.append_assoc]

/-- The stored Z row emits its complete canonical public table. -/
theorem publicZWire_bits (sample : RowPublicSample) (row : Nat) (ram : Word → Word) (pointer : Word)
    (stored : WordsAt ram pointer (1017 + 9920 * row) (rowSchedule.words sample)) :
    (publicZWire row).flatMap (WireSegment.wire ram pointer) =
      (Wire.biquadratic.encode sample.z.request.table).flatMap (fun byte => bits 8 byte.val) := by
  let base := 1017 + 9920 * row
  have source := row_z_words sample ram pointer base stored
  have coefficient (index : Fin 5) :
      ram (pointer + BitVec.ofNat 256 (base + 3810 + index.val)) =
        BitVec.ofNat 256 (sample.z.coefficients index).val := by
    simpa only [coordinateBitCount, Nat.reduceMul, Nat.reduceAdd, Nat.add_assoc] using
      gateData_coefficient 5 5 _ ram pointer (base + 0) index source
  have table (gate : Fin 5) (index : Fin coordinateBitCount) :
      ram (pointer + BitVec.ofNat 256 (base + 2540 + 254 * gate.val + index.val)) =
        ((sample.z.tables gate).get index).trueRow := by
    simpa only [coordinateBitCount, Nat.reduceMul, Nat.reduceAdd, Nat.add_assoc] using
      gateData_table 5 5 _ ram pointer (base + 0) gate index source
  simp only [publicZWire, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    ZPublicSample.request, BiquadraticZRequest.table]
  rw [Wire.biquadratic_encode_z]
  simp only [List.flatMap_cons, List.flatMap_append, List.flatMap_nil, List.append_nil]
  rw [wireHeader_bits, wireCoefficient_bits ram pointer (base + 3810) 0 _ (coefficient 0),
    wireCoefficient_bits ram pointer (base + 3810) 1 _ (coefficient 1),
    wireCoefficient_bits ram pointer (base + 3810) 2 _ (coefficient 2),
    wireCoefficient_bits ram pointer (base + 3810) 3 _ (coefficient 3),
    wireCoefficient_bits ram pointer (base + 3810) 4 _ (coefficient 4),
    wireOptionalDigit_bits ram pointer (base + 2540) 3 _ (table 3),
    wireOptionalDigit_bits ram pointer (base + 2540) 4 _ (table 4),
    wireOptionalDigit_bits ram pointer (base + 2540) 0 _ (table 0),
    wireOptionalDigit_bits ram pointer (base + 2540) 1 _ (table 1),
    wireOptionalDigit_bits ram pointer (base + 2540) 2 _ (table 2)]
  simp [List.append_assoc]

end Kriterion.ArgoMAC.ArithmeticSimulator
