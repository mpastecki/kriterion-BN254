import Proof.Correctness.YCubic
import Proof.Privacy.Distribution.MaskFiber

namespace Kriterion.ArgoMAC.Security.CubicMasks

open BN254

noncomputable section

abbrev Masks := Fin 3 → Fin coordinateBitCount → BaseField
abbrev Source := (Fin 3 → BaseField) × Masks
abbrev View := (Fin 4 → BaseField) × Masks

def coefficients (c : Cubic.Coefficients) : Fin 3 → BaseField := ![c.c1, c.c2, c.c3]

/-- The inverse follows the chain from its highest degree to its terminal mask. -/
def selectedEquiv (c : Cubic.Coefficients) (x : BaseField) : Source ≃ Source where
  toFun source := ((fun index => coefficients c index + source.1 index),
    ![maskShiftEquiv (-source.1 2) x (source.2 0),
      maskShiftEquiv (-(source.1 1 + DigitAdaptor.fromBits (source.2 0))) x (source.2 1),
      maskShiftEquiv (-(source.1 0 + DigitAdaptor.fromBits (source.2 1))) x (source.2 2)])
  invFun selected :=
    let r := fun index => selected.1 index - coefficients c index
    let high := (maskShiftEquiv (-r 2) x).symm (selected.2 0)
    let middle := (maskShiftEquiv (-(r 1 + DigitAdaptor.fromBits high)) x).symm (selected.2 1)
    (r, ![high, middle,
      (maskShiftEquiv (-(r 0 + DigitAdaptor.fromBits middle)) x).symm (selected.2 2)])
  left_inv source := by
    apply Prod.ext
    · funext index; simp
    · funext index; fin_cases index <;> simp
  right_inv selected := by
    apply Prod.ext
    · funext index; simp
    · funext index; fin_cases index <;> simp

def rest (x : BaseField) (data : Source) : BaseField :=
  data.1 0 * x + data.1 1 * x ^ 2 + data.1 2 * x ^ 3 +
    DigitAdaptor.fromBits (data.2 0) * x ^ 2 +
    DigitAdaptor.fromBits (data.2 1) * x + DigitAdaptor.fromBits (data.2 2)

def result (x : BaseField) (view : View) : BaseField :=
  view.1 0 + rest x ((fun index => view.1 index.succ), view.2)

def garbleEquiv (c : Cubic.Coefficients) (x : BaseField) :
    Source ≃ {view : View // result x view = Cubic.polynomial c x} :=
  (selectedEquiv c x).trans (maskViewFiberEquiv (rest x) (Cubic.polynomial c x))

def publicCoefficients (c : Cubic.Coefficients) (source : Source) : Fin 4 → BaseField :=
  Fin.cases (c.c0 - DigitAdaptor.fromBits (source.2 2))
    (fun index => coefficients c index + source.1 index)

/-- The source map publishes the same coefficients before any input is selected. -/
theorem garbleEquiv_coefficients (c : Cubic.Coefficients) (x : BaseField) (source : Source) :
    (garbleEquiv c x source).1.1 = publicCoefficients c source := by
  funext index
  refine Fin.cases ?_ (fun _ => rfl) index
  change Cubic.polynomial c x -
    ((coefficients c 0 + source.1 0) * x + (coefficients c 1 + source.1 1) * x ^ 2 +
      (coefficients c 2 + source.1 2) * x ^ 3 +
      DigitAdaptor.fromBits (maskShiftEquiv (-source.1 2) x (source.2 0)) * x ^ 2 +
      DigitAdaptor.fromBits (maskShiftEquiv (-(source.1 1 + DigitAdaptor.fromBits (source.2 0)))
        x (source.2 1)) * x +
      DigitAdaptor.fromBits (maskShiftEquiv (-(source.1 0 + DigitAdaptor.fromBits (source.2 1)))
        x (source.2 2))) = c.c0 - DigitAdaptor.fromBits (source.2 2)
  rw [fromBits_maskShift, fromBits_maskShift, fromBits_maskShift]
  simp [coefficients, Cubic.polynomial]
  ring

def actualSource (randomness : Cubic.Randomness) (oracles : Cubic.Oracles)
    (key : CoordinateMacKey) : Source :=
  (![randomness.r1, randomness.r2, randomness.r3],
    ![(fun index => (oracles.high index.val).hashToField (key.get index).falseLabel),
      (fun index => (oracles.middle index.val).hashToField (key.get index).falseLabel),
      (fun index => (oracles.low index.val).hashToField (key.get index).falseLabel)])

/-- This identifies the source map with the actual three-adaptor garbler. -/
theorem actual_publicCoefficients (c : Cubic.Coefficients) (randomness : Cubic.Randomness)
    (oracles : Cubic.Oracles) (key : CoordinateMacKey) :
    let table := Cubic.garble c randomness oracles key
    ![table.coefficients.c0, table.coefficients.c1, table.coefficients.c2, table.coefficients.c3] =
      publicCoefficients c (actualSource randomness oracles key) := by
  funext index
  fin_cases index <;>
    simp [Cubic.garble, publicCoefficients, actualSource, coefficients,
      DigitAdaptor.bitsK, DigitAdaptor.garble, BitAdaptor.garble] <;> rfl

def actualTargets (randomness : Cubic.Randomness) (oracles : Cubic.Oracles)
    (key : CoordinateMacKey) (x : BaseField) : Masks :=
  let high := DigitAdaptor.garble oracles.high (-randomness.r3) key
  let middle := DigitAdaptor.garble oracles.middle
    (-(randomness.r2 + DigitAdaptor.bitsK high.2)) key
  let low := DigitAdaptor.garble oracles.low
    (-(randomness.r1 + DigitAdaptor.bitsK middle.2)) key
  ![(fun index => (DigitAdaptor.selectedOutputs high.2 (coordinateValues x)).get index),
    (fun index => (DigitAdaptor.selectedOutputs middle.2 (coordinateValues x)).get index),
    (fun index => (DigitAdaptor.selectedOutputs low.2 (coordinateValues x)).get index)]

/-- The finite source map contains the actual selected outputs of all three adaptors. -/
theorem actualTargets_eq (c : Cubic.Coefficients) (randomness : Cubic.Randomness)
    (oracles : Cubic.Oracles) (key : CoordinateMacKey) (x : BaseField) :
    actualTargets randomness oracles key x =
      (garbleEquiv c x (actualSource randomness oracles key)).1.2 := by
  simp only [actualTargets, digitGarble_selectedOutputs_eq, digitGarble_bitsK_eq]
  rfl

def pivotShift (amount : BaseField) (view : View) : View :=
  (view.1, Function.update view.2 2 (lowMaskShift amount (view.2 2)))

@[simp] theorem pivotShift_zero (view : View) : pivotShift 0 view = view := by
  simp [pivotShift]

theorem pivotShift_add (first second : BaseField) (view : View) :
    pivotShift first (pivotShift second view) = pivotShift (first + second) view := by
  apply Prod.ext
  · rfl
  · funext index
    by_cases pivot : index = 2
    · subst index; simp [pivotShift, lowMaskShift_add]
    · simp [pivotShift, pivot]

theorem result_pivotShift (x amount : BaseField) (view : View) :
    result x (pivotShift amount view) = result x view + amount := by
  change view.1 0 + (view.1 1 * x + view.1 2 * x ^ 2 + view.1 3 * x ^ 3 +
      DigitAdaptor.fromBits (view.2 0) * x ^ 2 + DigitAdaptor.fromBits (view.2 1) * x +
      DigitAdaptor.fromBits (lowMaskShift amount (view.2 2))) =
    view.1 0 + (view.1 1 * x + view.1 2 * x ^ 2 + view.1 3 * x ^ 3 +
      DigitAdaptor.fromBits (view.2 0) * x ^ 2 + DigitAdaptor.fromBits (view.2 1) * x +
      DigitAdaptor.fromBits (view.2 2)) + amount
  rw [fromBits_lowMaskShift]
  ring

def retarget (x target : BaseField) (view : View) : View :=
  pivotShift (target - result x view) view

@[simp] theorem retarget_coefficients (x target : BaseField) (view : View) :
    (retarget x target view).1 = view.1 := rfl

@[simp] theorem retarget_result (x target : BaseField) (view : View) :
    result x (retarget x target view) = target := by
  rw [retarget, result_pivotShift]
  ring

/-- Uniform source masks and terminal retargeting have exactly the same law. -/
theorem garble_eq_retargetDistribution (c : Cubic.Coefficients) (x : BaseField) :
    (PMF.uniformOfFintype Source).map (fun source => (garbleEquiv c x source).1) =
      (PMF.uniformOfFintype View).map (retarget x (Cubic.polynomial c x)) := by
  let e := garbleEquiv c x
  let : Nonempty {view : View // result x view = Cubic.polynomial c x} := ⟨e (0, 0)⟩
  change (PMF.uniformOfFintype Source).map (fun source => (garbleEquiv c x source).1) =
    (PMF.uniformOfFintype View).map (fun view =>
      pivotShift (Cubic.polynomial c x - result x view) view)
  rw [map_uniform_retargetOfShift (result x) pivotShift
    pivotShift_zero pivotShift_add (result_pivotShift x),
    ← map_uniformOfFintype_equivBetween e, PMF.map_comp]
  rfl

/-- The request retains the complete public ciphertext table. -/
structure Request where
  table : Cubic.Table
  targets : Masks

def Request.view (request : Request) : View :=
  (![request.table.coefficients.c0, request.table.coefficients.c1,
    request.table.coefficients.c2, request.table.coefficients.c3], request.targets)

def actualRequest (c : Cubic.Coefficients) (randomness : Cubic.Randomness)
    (oracles : Cubic.Oracles) (key : CoordinateMacKey) (x : BaseField) : Request :=
  ⟨Cubic.garble c randomness oracles key, actualTargets randomness oracles key x⟩

theorem actualRequest_view (c : Cubic.Coefficients) (randomness : Cubic.Randomness)
    (oracles : Cubic.Oracles) (key : CoordinateMacKey) (x : BaseField) :
    (actualRequest c randomness oracles key x).view =
      (garbleEquiv c x (actualSource randomness oracles key)).1 := by
  apply Prod.ext
  · rw [garbleEquiv_coefficients]
    exact actual_publicCoefficients c randomness oracles key
  · exact actualTargets_eq c randomness oracles key x

def Request.retarget (request : Request) (x target : BaseField) : Request :=
  { request with targets := (CubicMasks.retarget x target request.view).2 }

@[simp] theorem Request.retarget_table (request : Request) (x target : BaseField) :
    (request.retarget x target).table = request.table := rfl

theorem Request.retarget_view (request : Request) (x target : BaseField) :
    (request.retarget x target).view = CubicMasks.retarget x target request.view := rfl

@[simp] theorem Request.retarget_result (request : Request) (x target : BaseField) :
    result x (request.retarget x target).view = target := by
  rw [Request.retarget_view, CubicMasks.retarget_result]

/-- Retain arbitrary ciphertext rows while the algebraic mask map changes its input. -/
def sourceTable (c : Cubic.Coefficients) (source : Source)
    (tables : Fin 3 → Vector BitAdaptor.Table coordinateBitCount) : Cubic.Table :=
  { coefficients := ⟨publicCoefficients c source 0, publicCoefficients c source 1,
      publicCoefficients c source 2, publicCoefficients c source 3⟩
    high := tables 0
    middle := tables 1
    low := tables 2 }

def sourceRequest (c : Cubic.Coefficients) (x : BaseField) (source : Source)
    (tables : Fin 3 → Vector BitAdaptor.Table coordinateBitCount) : Request :=
  { table := sourceTable c source tables
    targets := (garbleEquiv c x source).1.2 }

theorem sourceRequest_view (c : Cubic.Coefficients) (x : BaseField) (source : Source)
    (tables : Fin 3 → Vector BitAdaptor.Table coordinateBitCount) :
    (sourceRequest c x source tables).view = (garbleEquiv c x source).1 := by
  apply Prod.ext
  · rw [garbleEquiv_coefficients]
    funext index
    fin_cases index <;> rfl
  · rfl

theorem sourceRequest_result (c : Cubic.Coefficients) (x : BaseField) (source : Source)
    (tables : Fin 3 → Vector BitAdaptor.Table coordinateBitCount) :
    result x (sourceRequest c x source tables).view = Cubic.polynomial c x := by
  rw [sourceRequest_view]
  exact (garbleEquiv c x source).2

/-- This statement includes arbitrary off-curve dummy inputs. -/
theorem sourceRequest_table_input (c : Cubic.Coefficients) (first second : BaseField)
    (source : Source) (tables : Fin 3 → Vector BitAdaptor.Table coordinateBitCount) :
    (sourceRequest c first source tables).table = (sourceRequest c second source tables).table := rfl

end

end Kriterion.ArgoMAC.Security.CubicMasks
