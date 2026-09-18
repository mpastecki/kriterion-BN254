import Proof.Privacy.Simulator.Arithmetic.PublicWire

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol Security
attribute [local irreducible] Encoding.natural Encoding.vector Wire.field Wire.adaptor Wire.digit
  Wire.biquadratic Wire.curve Wire.pointMAC Wire.encoding

/-- Each sampled X row has the canonical public length. -/
theorem publicXEncoded_length (sample : XPublicSample) :
    (Wire.biquadratic.encode sample.request.table).length = 32673 := by
  simp [XPublicSample.request, BiquadraticXRequest.table, Wire.biquadratic_encode_x]

/-- Each sampled Y row has the canonical public length. -/
theorem publicYEncoded_length (sample : YPublicSample) :
    (Wire.biquadratic.encode sample.request.table).length = 32641 := by
  simp [YPublicSample.request, BiquadraticYRequest.table, Wire.biquadratic_encode_y]

/-- Each sampled Z row has the canonical public length. -/
theorem publicZEncoded_length (sample : ZPublicSample) :
    (Wire.biquadratic.encode sample.request.table).length = 40801 := by
  simp [ZPublicSample.request, BiquadraticZRequest.table, Wire.biquadratic_encode_z]

/-- Every sampled public table has exactly 9803316 canonical bytes. -/
theorem publicSourceTable_length (sample : PublicSample) :
    (Wire.encoding.encode (publicSourceTable sample)).length = 9803316 := by
  have curve : (Wire.curve.encode sample.curveRequest.table).length = 40736 := Wire.curve_length _
  let rows := pointGateTable sample.pointRequests
  have x : ((Wire.biquadratic.vector FieldMacToECMac.outputMacCount).encode rows.x).length =
      FieldMacToECMac.outputMacCount * 32673 := by
    apply Encoding.vector_length
    intro index
    simpa only [rows, pointGateTable, PublicSample.pointRequests, Vector.get_ofFn, Vector.get_map,
      BiquadraticRowRequest.table, RowPublicSample.request] using publicXEncoded_length (sample.points.get index).x
  have y : ((Wire.biquadratic.vector FieldMacToECMac.outputMacCount).encode rows.y).length =
      FieldMacToECMac.outputMacCount * 32641 := by
    apply Encoding.vector_length
    intro index
    simpa only [rows, pointGateTable, PublicSample.pointRequests, Vector.get_ofFn, Vector.get_map,
      BiquadraticRowRequest.table, RowPublicSample.request] using publicYEncoded_length (sample.points.get index).y
  have z : ((Wire.biquadratic.vector FieldMacToECMac.outputMacCount).encode rows.z).length =
      FieldMacToECMac.outputMacCount * 40801 := by
    apply Encoding.vector_length
    intro index
    simpa only [rows, pointGateTable, PublicSample.pointRequests, Vector.get_ofFn, Vector.get_map,
      BiquadraticRowRequest.table, RowPublicSample.request] using publicZEncoded_length (sample.points.get index).z
  simp only [Wire.encoding, Wire.pointMAC, publicSourceTable, Encoding.map, Encoding.pair, List.length_append]
  change (Wire.curve.encode sample.curveRequest.table).length +
    (((Wire.biquadratic.vector FieldMacToECMac.outputMacCount).encode rows.x).length +
    (((Wire.biquadratic.vector FieldMacToECMac.outputMacCount).encode rows.y).length +
      ((Wire.biquadratic.vector FieldMacToECMac.outputMacCount).encode rows.z).length)) = _
  rw [curve, x, y, z]
  rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
