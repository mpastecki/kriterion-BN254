import Proof.Privacy.Simulator.Arithmetic.OnlineSamplingMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The scale phase occupies the first 3588 instruction slots. -/
def onlineScaleLabels (pc : Fin 3589) : Fin 8869 := ⟨pc.val, by have h := pc.isLt; omega⟩

/-- The point phase starts after the two pointer-change instructions. -/
def onlinePointLabels (pc : Fin 5279) : Fin 8869 := ⟨pc.val + 3590, by have h := pc.isLt; omega⟩

/-- The online sampler stores 92 scales and 91 points in one fixed arithmetic program. -/
def onlineCode (attempts : Nat) : Vector (Instruction 8869) 8869 :=
  Vector.ofFn (fun pc : Fin 8869 =>
    if scales : pc.val < 3588 then
      relocate onlineScaleLabels ((samplerBatch onlineScalePlan attempts (by decide)).code[pc.val]'(by change pc.val < 3589; omega))
    else if pc.val = 3588 then .constant 8 92 3589
    else if pc.val = 3589 then .arithmetic .add 10 10 8 3590
    else if points : pc.val < 8868 then relocate onlinePointLabels ((pointBatch 91 attempts (by decide)).code[pc.val - 3590]'(by
      change pc.val - 3590 < 5279
      have h := pc.isLt
      omega)) else .halt)

/-- The online machine keeps its fixed size separate from its instruction table. -/
def onlineSampling (attempts : Nat) : Machine := ⟨8868, onlineCode attempts, by decide⟩

/-- A host contains every online instruction before the final return. -/
def ContainsOnlineSampling (host : Machine) (attempts : Nat) (labels : Fin 8869 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 8869, pc.val < 8868 →
    host.code[(labels pc).val] = relocate labels ((onlineSampling attempts).code[pc.val])

/-- The host contains the full scale batch. -/
theorem onlineSamplingBlock_scales (host : Machine) (attempts : Nat) (labels : Fin 8869 → Fin (host.size + 1))
    (present : ContainsOnlineSampling host attempts labels) :
    ContainsSamplerBatch host onlineScalePlan attempts (by decide) (labels ∘ onlineScaleLabels) := by
  intro pc inside
  have position : (onlineScaleLabels pc).val < 8868 := by
    change pc.val < 8868
    change pc.val < 3588 at inside
    omega
  have source : (onlineSampling attempts).code[(onlineScaleLabels pc).val] =
      relocate onlineScaleLabels ((samplerBatch onlineScalePlan attempts (by decide)).code[pc.val]) := by
    simp [onlineSampling, onlineCode, onlineScaleLabels, inside]
  exact ((present (onlineScaleLabels pc) position).trans (congrArg (relocate labels) source)).trans
    (relocate_comp onlineScaleLabels labels _)

/-- The host contains the full point batch. -/
theorem onlineSamplingBlock_points (host : Machine) (attempts : Nat) (labels : Fin 8869 → Fin (host.size + 1))
    (present : ContainsOnlineSampling host attempts labels) :
    ContainsPointBatch host 91 attempts (by decide) (labels ∘ onlinePointLabels) := by
  intro pc inside
  have bound := pc.isLt
  have position : (onlinePointLabels pc).val < 8868 := by
    change pc.val + 3590 < 8868
    change pc.val < 5278 at inside
    omega
  have source : (onlineSampling attempts).code[(onlinePointLabels pc).val] =
      relocate onlinePointLabels ((pointBatch 91 attempts (by decide)).code[pc.val]) := by
    simp [onlineSampling, onlineCode, onlinePointLabels, show ¬pc.val + 3590 < 3588 by omega, show pc.val + 3590 < 8868 by change pc.val < 5278 at inside; omega]
    rfl
  exact ((present (onlinePointLabels pc) position).trans (congrArg (relocate labels) source)).trans
    (relocate_comp onlinePointLabels labels _)

/-- The host changes the point destination pointer in two charged instructions. -/
theorem onlineSamplingBlock_pointer [BN254.FieldCertificate] (host : Machine) (attempts : Nat)
    (labels : Fin 8869 → Fin (host.size + 1)) (present : ContainsOnlineSampling host attempts labels)
    (fuel : Nat) (base : Memory) :
    run host (fuel + 2) ⟨labels 3588, base⟩ =
      (run host fuel ⟨labels 3590, onlinePointInitial base⟩).map
        (Option.map fun result => (result.1, result.2 + 2)) := by
  have first := present 3588 (by decide)
  have second := present 3589 (by decide)
  have sourceFirst : (onlineSampling attempts).code[3588]'(by change 3588 < 8869; decide) = .constant 8 92 3589 := by
    simp only [onlineSampling, onlineCode, Vector.getElem_ofFn]
    rfl
  have sourceSecond : (onlineSampling attempts).code[3589]'(by change 3589 < 8869; decide) = .arithmetic .add 10 10 8 3590 := by
    simp only [onlineSampling, onlineCode, Vector.getElem_ofFn]
    rfl
  change host.code[(labels 3588).val] = relocate labels ((onlineSampling attempts).code[3588]'(by change 3588 < 8869; decide)) at first
  change host.code[(labels 3589).val] = relocate labels ((onlineSampling attempts).code[3589]'(by change 3589 < 8869; decide)) at second
  rw [sourceFirst] at first
  rw [sourceSecond] at second
  change host.code[(labels 3588).val] = .constant 8 92 (labels 3589) at first
  change host.code[(labels 3589).val] = .arithmetic .add 10 10 8 (labels 3590) at second
  simp [run, step, first, second, relocate, Arithmetic.eval, onlinePointInitial,
    PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

end Kriterion.ArgoMAC.ArithmeticSimulator
