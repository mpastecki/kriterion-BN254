import Proof.Privacy.Simulator.Arithmetic.PublicRowWire

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol Security
set_option maxRecDepth 4096

/-- The fixed row schedule emits each encoded row in its array order. -/
theorem publicWire_rows (count : Nat) (schedule : Nat → List WireSegment)
    (tables : Vector Biquadratic.Table count) (ram : Word → Word) (pointer : Word)
    (row : ∀ index : Fin count,
      (schedule index.val).flatMap (WireSegment.wire ram pointer) =
        (Wire.biquadratic.encode (tables.get index)).flatMap (fun byte => bits 8 byte.val)) :
    ((List.range count).flatMap schedule).flatMap (WireSegment.wire ram pointer) =
      ((Wire.biquadratic.vector count).encode tables).flatMap (fun byte => bits 8 byte.val) := by
  rw [vectorEncoding_encode, List.flatMap_assoc, List.flatMap_assoc]
  rw [List.flatMap_def, List.flatMap_def]
  congr 1
  apply List.ext_getElem
  · simp
  · intro index left right
    have inside : index < count := by simpa using left
    simp only [List.getElem_map, List.getElem_range]
    exact row ⟨index, inside⟩

/-- The public source table uses all curve, X, Y, and Z entries. -/
def publicSourceTable (sample : PublicSample) : Pipeline.Table :=
  ⟨sample.curveRequest.table, pointGateTable sample.pointRequests⟩

/-- The fixed public schedule emits exactly the complete canonical ciphertext. -/
theorem publicWire_bits (sample : PublicSample) (ram : Word → Word) (pointer : Word)
    (stored : WordsAt ram pointer 1017 (publicSchedule.words sample)) :
    publicWire.flatMap (WireSegment.wire ram pointer) =
      (Wire.encoding.encode (publicSourceTable sample)).flatMap (fun byte => bits 8 byte.val) := by
  have x := publicWire_rows 92 publicXWire (pointGateTable sample.pointRequests).x ram pointer (by
    intro index
    simpa only [pointGateTable, PublicSample.pointRequests, Vector.get_ofFn, Vector.get_map,
      BiquadraticRowRequest.table, RowPublicSample.request] using
      publicXWire_bits (sample.points.get index) index.val ram pointer (public_row_words sample ram pointer index stored))
  have y := publicWire_rows 92 publicYWire (pointGateTable sample.pointRequests).y ram pointer (by
    intro index
    simpa only [pointGateTable, PublicSample.pointRequests, Vector.get_ofFn, Vector.get_map,
      BiquadraticRowRequest.table, RowPublicSample.request] using
      publicYWire_bits (sample.points.get index) index.val ram pointer (public_row_words sample ram pointer index stored))
  have z := publicWire_rows 92 publicZWire (pointGateTable sample.pointRequests).z ram pointer (by
    intro index
    simpa only [pointGateTable, PublicSample.pointRequests, Vector.get_ofFn, Vector.get_map,
      BiquadraticRowRequest.table, RowPublicSample.request] using
      publicZWire_bits (sample.points.get index) index.val ram pointer (public_row_words sample ram pointer index stored))
  simp only [publicWire, List.flatMap_append]
  rw [publicCurveWire_bits sample ram pointer stored, x, y, z]
  simp only [Wire.encoding, Wire.pointMAC, publicSourceTable, Encoding.map, Encoding.pair,
    List.flatMap_append, List.append_assoc]

end Kriterion.ArgoMAC.ArithmeticSimulator
