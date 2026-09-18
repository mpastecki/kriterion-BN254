import Proof.Privacy.Simulator.Arithmetic.PublicLayout
import Proof.Privacy.Simulator.Arithmetic.PublicWireBlocks

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol Security

/-- The stored curve sample emits its complete canonical public table. -/
theorem publicCurveWire_bits (sample : PublicSample) (ram : Word → Word) (pointer : Word)
    (stored : WordsAt ram pointer 1017 (publicSchedule.words sample)) :
    publicCurveWire.flatMap (WireSegment.wire ram pointer) =
      (Wire.curve.encode sample.curveRequest.table).flatMap (fun byte => bits 8 byte.val) := by
  have curve := public_curve_words sample ram pointer stored
  have coefficient (index : Fin 3) :
      ram (pointer + BitVec.ofNat 256 (917467 + index.val)) = BitVec.ofNat 256 (sample.curve.coefficients index).val := by
    exact gateData_coefficient 3 5 _ ram pointer 913657 index curve
  have table (gate : Fin 5) (index : Fin coordinateBitCount) :
      ram (pointer + BitVec.ofNat 256 (916197 + 254 * gate.val + index.val)) =
        ((sample.curve.tables gate).get index).trueRow := by
    exact gateData_table 3 5 _ ram pointer 913657 gate index curve
  simp only [publicCurveWire, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Wire.curve, Encoding.map, Encoding.pair, PublicSample.curveRequest, CurvePublicSample.request,
    CurveGateRequest.table]
  rw [wireStored_field ram pointer 917467 _ (coefficient 0),
    wireStored_field ram pointer 917468 _ (coefficient 1),
    wireStored_field ram pointer 917469 _ (coefficient 2),
    wireDigit_bits ram pointer 916197 _ (table 0),
    wireDigit_bits ram pointer 916451 _ (table 1),
    wireDigit_bits ram pointer 916705 _ (table 2),
    wireDigit_bits ram pointer 916959 _ (table 3),
    wireDigit_bits ram pointer 917213 _ (table 4)]
  simp only [List.append_assoc]

end Kriterion.ArgoMAC.ArithmeticSimulator
