import Construction.Simulator.ClampPoint
import Construction.Simulator.HomogeneousRows

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The Horner block starts at the machine entry. -/
def targetHornerLabels (pc : Fin 2008) : Fin 4336 := ⟨pc.val, by omega⟩

/-- The correction block follows the Horner block. -/
def targetClampLabels (pc : Fin 27) : Fin 4336 := ⟨2007 + pc.val, by omega⟩

/-- The row block follows the scale-pointer instruction. -/
def targetRowLabels (pc : Fin 2302) : Fin 4336 := ⟨2034 + pc.val, by omega⟩

/-- The machine computes all output targets from the sampled points and scales.
Register ten points to the free points. Register eleven points to the input record.
Register fourteen points to the scales. Register thirteen points to the destination. -/
def outputTargetsMachine : Machine := ⟨4335, Vector.ofFn (fun pc : Fin 4336 =>
  if horner : pc.val < 2007 then
    relocate targetHornerLabels ((pointHornerMachine 91 (by decide)).code[pc.val]'(by change pc.val < 2008; omega))
  else if correction : pc.val < 2033 then
    relocate targetClampLabels (clampPoint.code[pc.val - 2007]'(by change pc.val - 2007 < 27; omega))
  else if pointer : pc.val = 2033 then .arithmetic .add 11 14 9 2034
  else if rows : pc.val < 4335 then
    relocate targetRowLabels ((homogeneousRows 91 (by decide)).code[pc.val - 2034]'(by change pc.val - 2034 < 2302; omega))
  else .halt), by decide⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
