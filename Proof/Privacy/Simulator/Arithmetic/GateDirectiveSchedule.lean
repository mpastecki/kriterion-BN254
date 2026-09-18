import Proof.Privacy.Programming.ActualScheduleRecords
import Proof.Privacy.Simulator.Arithmetic.SharedGateLoopCommands

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Security

private theorem ofFn_five {A : Type} (f : Fin 5 → A) :
    List.ofFn f = [f 0, f 1, f 2, f 3, f 4] := by
  simp [List.ofFn_succ]

private theorem ofFn_thirteen {A : Type} (f : Fin 13 → A) :
    List.ofFn f = [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12] := by
  simp [List.ofFn_succ]

/-- The curve loop visits each adaptor before it advances to the next adaptor. -/
def curveDirectiveAt (request : CurveGateRequest) (input : AffineInput) (mac : InputMac)
    (index : Fin 1270) : GateDirective :=
  request.actualDirective input mac ⟨index.val / 254, by have := index.isLt; omega⟩
    ⟨index.val % 254, Nat.mod_lt _ (by decide)⟩

/-- Each point row visits its four x, four y, and five z adaptors. -/
def pointRowDirectiveAt (request : BiquadraticRowRequest) (row : Fin 92)
    (input : AffineInput) (mac : InputMac) (gate : Fin 13) (bit : Fin 254) : GateDirective :=
  if first : gate.val < 4 then request.x.actualDirective row input mac ⟨gate.val, first⟩ bit
  else if second : gate.val < 8 then request.y.actualDirective row input mac ⟨gate.val - 4, by omega⟩ bit
  else request.z.actualDirective row input mac ⟨gate.val - 8, by have := gate.isLt; omega⟩ bit

/-- The point loop visits all 92 rows in the source order. -/
def pointDirectiveAt (requests : PointGateRequests) (input : AffineInput) (mac : InputMac)
    (index : Fin 303784) : GateDirective :=
  let row : Fin 92 := ⟨index.val / 3302, by have := index.isLt; omega⟩
  pointRowDirectiveAt (requests.get row) row input mac
    ⟨index.val % 3302 / 254, by have := Nat.mod_lt index.val (by decide : 0 < 3302); omega⟩
    ⟨index.val % 254, Nat.mod_lt _ (by decide)⟩

/-- The flattened curve loop has the exact source schedule. -/
theorem curveDirectiveAt_schedule (request : CurveGateRequest) (input : AffineInput) (mac : InputMac) :
    List.ofFn (curveDirectiveAt request input mac) = request.schedule input mac := by
  rw [List.ofFn_mul (m := 5) (n := 254)]
  have rows : (fun gate : Fin 5 => List.ofFn fun bit : Fin 254 =>
      curveDirectiveAt request input mac ⟨gate.val * 254 + bit.val, by have := gate.isLt; have := bit.isLt; omega⟩) =
      (fun gate : Fin 5 => List.ofFn (request.actualDirective input mac gate)) := by
    funext gate
    congr 1
    funext bit
    unfold curveDirectiveAt
    congr 1 <;> apply Fin.ext <;> simp [Nat.add_div, Nat.div_eq_of_lt bit.isLt, Nat.mod_eq_of_lt bit.isLt]
  rw [rows]
  rw [ofFn_five]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, CurveGateRequest.actualDirective, CurveGateRequest.schedule,
    digitGateSchedule, actualDigitDirective, List.append_assoc]
  rfl

/-- The thirteen adaptor rows have the exact point-row source schedule. -/
theorem pointRowDirectiveAt_schedule (request : BiquadraticRowRequest) (row : Fin 92)
    (input : AffineInput) (mac : InputMac) :
    (List.ofFn fun gate : Fin 13 => List.ofFn (pointRowDirectiveAt request row input mac gate)).flatten =
      request.schedule row input mac := by
  rw [ofFn_thirteen]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, pointRowDirectiveAt, BiquadraticRowRequest.schedule, biquadraticRowGateSchedule,
    BiquadraticXRequest.schedule, BiquadraticYRequest.schedule, BiquadraticZRequest.schedule,
    biquadraticXGateSchedule, biquadraticYGateSchedule, biquadraticZGateSchedule,
    BiquadraticXRequest.actualDirective, BiquadraticYRequest.actualDirective, BiquadraticZRequest.actualDirective,
    digitGateSchedule, actualDigitDirective, List.append_assoc]
  rfl

/-- The flattened point index selects its exact row, adaptor, and bit. -/
theorem pointDirectiveAt_row (requests : PointGateRequests) (input : AffineInput) (mac : InputMac)
    (row : Fin 92) (gate : Fin 13) (bit : Fin 254) :
    pointDirectiveAt requests input mac
      ⟨row.val * 3302 + (gate.val * 254 + bit.val), by
        have := row.isLt; have := gate.isLt; have := bit.isLt; omega⟩ =
      pointRowDirectiveAt (requests.get row) row input mac gate bit := by
  have rowBound := row.isLt
  have gateBound := gate.isLt
  have bitBound := bit.isLt
  unfold pointDirectiveAt
  have rowEq : (⟨(row.val * 3302 + (gate.val * 254 + bit.val)) / 3302, by omega⟩ : Fin 92) = row := by
    apply Fin.ext
    simp only [Fin.val_mk]
    omega
  simp only [rowEq]
  congr 1 <;> apply Fin.ext <;> simp only [Fin.val_mk] <;> omega

/-- The flattened point loop has the exact source schedule. -/
theorem pointDirectiveAt_schedule (requests : PointGateRequests) (input : AffineInput) (mac : InputMac) :
    List.ofFn (pointDirectiveAt requests input mac) = pointGateSchedule requests input mac := by
  rw [List.ofFn_mul (m := 92) (n := 3302)]
  unfold pointGateSchedule
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext row
  rw [List.ofFn_mul (m := 13) (n := 254)]
  have rows : (fun gate : Fin 13 => List.ofFn fun bit : Fin 254 =>
      pointDirectiveAt requests input mac ⟨row.val * 3302 + (gate.val * 254 + bit.val), by
        have := row.isLt; have := gate.isLt; have := bit.isLt; omega⟩) =
      (fun gate : Fin 13 => List.ofFn (pointRowDirectiveAt (requests.get row) row input mac gate)) := by
    funext gate
    apply congrArg List.ofFn
    funext bit
    exact pointDirectiveAt_row requests input mac row gate bit
  rw [rows]
  exact pointRowDirectiveAt_schedule (requests.get row) row input mac

end Kriterion.ArgoMAC.ArithmeticSimulator
