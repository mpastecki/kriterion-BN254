import Construction.Simulator.GateLoop
import Construction.SharedGarbling

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography
noncomputable section

/-- Each fixed descriptor reads one source bit and its three sampled words. -/
def gateCodeAt (location : Pipeline.FixedKeyLocation) (isX : Bool)
    (start gates gate : Nat) (bit : Fin 254) : GateCode where
  selected := ⟨(if isX then 0 else 254) + bit.val, by split <;> have bound := bit.isLt <;> omega⟩
  target := start + 254 * gate + bit.val
  quotient := start + gates * 254 + 254 * gate + bit.val
  table := start + 2 * gates * 254 + 254 * gate + bit.val
  tweak := location.tweak
  oracle slot := (Fintype.equivFin Shared.FixedKeyIndex ⟨location.kind, bit, slot⟩).val

/-- The curve descriptors follow x3, x5, x7, y4, and y6 in source order. -/
def curveGateCode (gate : Fin 5) (bit : Fin 254) : GateCode :=
  gateCodeAt (.curve (match gate.val with | 0 => .x3 | 1 => .x5 | 2 => .x7 | 3 => .y4 | _ => .y6))
    (gate.val < 3) 913657 5 gate.val bit

/-- The point descriptors follow X, Y, and Z in each output row. -/
def pointGateCode (row : Fin 92) (gate : Fin 13) (bit : Fin 254) : GateCode :=
  let start := 1017 + 9920 * row.val
  if gate.val < 4 then
    gateCodeAt (.point row .x (match gate.val with | 0 => .y6 | 1 => .y8 | 2 => .y10 | _ => .x9))
      (gate.val = 3) (start + 6867) 4 gate.val bit
  else if gate.val < 8 then
    gateCodeAt (.point row .y (match gate.val - 4 with | 0 => .y8 | 1 => .y10 | 2 => .x7 | _ => .x9))
      (6 ≤ gate.val) (start + 3815) 4 (gate.val - 4) bit
  else
    gateCodeAt (.point row .z (match gate.val - 8 with | 0 => .y6 | 1 => .y8 | 2 => .y10 | 3 => .x7 | _ => .x9))
      (11 ≤ gate.val) start 5 (gate.val - 8) bit

/-- The curve phase has exactly 1270 descriptors. -/
def curveGatePlan : Vector GateCode 1270 := Vector.ofFn fun index =>
  curveGateCode ⟨index.val / 254, by have bound := index.isLt; omega⟩
    ⟨index.val % 254, by omega⟩

/-- The point phase has exactly 303784 descriptors across all 92 rows. -/
def pointGatePlan : Vector GateCode 303784 := Vector.ofFn fun index =>
  pointGateCode ⟨index.val / 3302, by have bound := index.isLt; omega⟩
    ⟨index.val % 3302 / 254, by omega⟩ ⟨index.val % 254, by omega⟩

end
end Kriterion.ArgoMAC.ArithmeticSimulator
