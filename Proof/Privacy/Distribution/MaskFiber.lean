import Proof.Privacy.Distribution.AlgebraicDistribution

namespace Kriterion.ArgoMAC.Security

open BN254

noncomputable section

/-- The bit-adaptor offsets are exactly its false-branch hash values. -/
theorem digitGarble_bitsK_eq {count : Nat} (windows : Nat → BitAdaptor.FixedKeyOracle)
    (slope : BaseField) (keys : Vector BitAdaptor.Key count) :
    DigitAdaptor.bitsK (DigitAdaptor.garble windows slope keys).2 =
      DigitAdaptor.fromBits (fun index =>
        (windows index.val).hashToField (keys.get index).falseLabel) := by
  simp [DigitAdaptor.bitsK, DigitAdaptor.garble, BitAdaptor.garble]

/-- The selected outputs apply the shared mask shift to those hash offsets. -/
theorem digitGarble_selectedOutputs_eq (windows : Nat → BitAdaptor.FixedKeyOracle)
    (slope input : BaseField) (keys : CoordinateMacKey) :
    (fun index => (DigitAdaptor.selectedOutputs
      (DigitAdaptor.garble windows slope keys).2 (coordinateValues input)).get index) =
      maskShiftEquiv slope input (fun index =>
        (windows index.val).hashToField (keys.get index).falseLabel) := by
  funext index
  simp [DigitAdaptor.selectedOutputs, DigitAdaptor.garble, BitAdaptor.garble,
    BitAdaptor.OutputKey.encode, maskShiftEquiv]

/-- The output fixes the constant coefficient once all other values are known. -/
def maskViewFiberEquiv {count : Nat} {Masks : Type*}
    (rest : (Fin count → BaseField) × Masks → BaseField) (target : BaseField) :
    ((Fin count → BaseField) × Masks) ≃
      {view : (Fin (count + 1) → BaseField) × Masks //
        view.1 0 + rest ((fun index => view.1 index.succ), view.2) = target} where
  toFun data := ⟨(Fin.cases (target - rest data) data.1, data.2), by simp⟩
  invFun view := ((fun index => view.1.1 index.succ), view.1.2)
  left_inv _ := rfl
  right_inv view := by
    apply Subtype.ext
    apply Prod.ext
    · funext index
      refine Fin.cases ?_ (fun _ => rfl) index
      change target - rest ((fun index => view.1.1 index.succ), view.1.2) = view.1.1 0
      exact sub_eq_iff_eq_add.mpr view.2.symm
    · rfl

/-- An additive pivot separates the result from a fixed result fiber. -/
def resultFiberSplitEquiv {View : Type*} (result : View → BaseField)
    (shift : BaseField → View → View)
    (shiftZero : ∀ view, shift 0 view = view)
    (shiftAdd : ∀ first second view, shift first (shift second view) = shift (first + second) view)
    (resultShift : ∀ amount view, result (shift amount view) = result view + amount)
    (target : BaseField) : View ≃ BaseField × {view // result view = target} where
  toFun view := (result view, ⟨shift (target - result view) view, by rw [resultShift]; ring⟩)
  invFun pair := shift (pair.1 - target) pair.2.1
  left_inv view := by
    change shift (result view - target) (shift (target - result view) view) = view
    rw [shiftAdd]
    have cancel : result view - target + (target - result view) = 0 := by ring
    rw [cancel, shiftZero]
  right_inv pair := by
    apply Prod.ext
    · change result (shift (pair.1 - target) pair.2.1) = pair.1
      rw [resultShift, pair.2.2]
      ring
    · apply Subtype.ext
      change shift (target - result (shift (pair.1 - target) pair.2.1))
        (shift (pair.1 - target) pair.2.1) = pair.2.1
      rw [resultShift, pair.2.2, shiftAdd]
      have cancel : target - (target + (pair.1 - target)) + (pair.1 - target) = 0 := by ring
      rw [cancel, shiftZero]

/-- Retargeting an additive pivot gives the uniform distribution on its result fiber. -/
theorem map_uniform_retargetOfShift {View : Type*} [Fintype View] [Nonempty View]
    (result : View → BaseField) (shift : BaseField → View → View)
    (shiftZero : ∀ view, shift 0 view = view)
    (shiftAdd : ∀ first second view, shift first (shift second view) = shift (first + second) view)
    (resultShift : ∀ amount view, result (shift amount view) = result view + amount)
    (target : BaseField) :
    letI : Nonempty {view // result view = target} :=
      ⟨(resultFiberSplitEquiv result shift shiftZero shiftAdd resultShift target
        (Classical.arbitrary View)).2⟩
    (PMF.uniformOfFintype View).map (fun view => shift (target - result view) view) =
      (PMF.uniformOfFintype {view // result view = target}).map Subtype.val := by
  classical
  let e := resultFiberSplitEquiv result shift shiftZero shiftAdd resultShift target
  letI : Nonempty {view // result view = target} := ⟨(e (Classical.arbitrary View)).2⟩
  calc
    _ = ((PMF.uniformOfFintype View).map e).map (Subtype.val ∘ Prod.snd) := by
      rw [PMF.map_comp]
      rfl
    _ = (PMF.uniformOfFintype (BaseField × {view // result view = target})).map
        (Subtype.val ∘ Prod.snd) := by
      rw [map_uniformOfFintype_equivBetween e]
    _ = _ := by rw [← PMF.map_comp, map_uniform_prod_snd]

/-- This shift adds to the low mask and keeps all other masks. -/
def lowMaskShift {count : Nat} (amount : BaseField)
    (values : Fin (count + 1) → BaseField) : Fin (count + 1) → BaseField :=
  Fin.cases (values 0 + amount) (fun index => values index.succ)

@[simp] theorem lowMaskShift_zero {count : Nat} (values : Fin (count + 1) → BaseField) :
    lowMaskShift 0 values = values := by
  funext index
  refine Fin.cases ?_ (fun _ => rfl) index
  simp [lowMaskShift]

theorem lowMaskShift_add {count : Nat} (first second : BaseField)
    (values : Fin (count + 1) → BaseField) :
    lowMaskShift first (lowMaskShift second values) = lowMaskShift (first + second) values := by
  funext index
  refine Fin.cases ?_ (fun _ => rfl) index
  simp only [lowMaskShift, Fin.cases_zero]
  ring

/-- The low-mask shift adds the same amount to the field total. -/
theorem fromBits_lowMaskShift {count : Nat} (amount : BaseField)
    (values : Fin (count + 1) → BaseField) :
    DigitAdaptor.fromBits (lowMaskShift amount values) = DigitAdaptor.fromBits values + amount := by
  simp only [DigitAdaptor.fromBits, Fin.foldr_succ, lowMaskShift, Fin.cases_zero, Fin.cases_succ]
  ring

/-- The low-mask shift is the simulator's retarget operation. -/
theorem lowMaskShift_eq_retargetBits {count : Nat} (amount : BaseField)
    (values : Fin (count + 1) → BaseField) :
    lowMaskShift amount values = retargetBits values (DigitAdaptor.fromBits values + amount) := by
  funext index
  refine Fin.cases ?_ (fun _ => rfl) index
  simp only [lowMaskShift, retargetBits, Fin.cases_zero, DigitAdaptor.fromBits, Fin.foldr_succ]
  ring

end

end Kriterion.ArgoMAC.Security
