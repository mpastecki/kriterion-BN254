import ScalarMultiplication
import Mathlib.Algebra.Module.Torsion.Free

namespace Kriterion.ScalarRecovery

open BN254

variable [FieldCertificate] [GroupCertificate]

local instance : Fact (Nat.Prime scalarFieldModulus) := ⟨scalarFieldPrime⟩

/-- A valid affine input never decodes as the identity. -/
theorem decodePoint_ne_zero (input : AffineInput) (point : Point)
    (decoded : decodePoint input = some point) : point ≠ 0 := by
  unfold decodePoint at decoded
  split at decoded
  · cases decoded
    intro h
    cases h
  · contradiction

/-- The pinned prime scalar field acts faithfully on each nonzero point. -/
theorem scalar_injective (point : Point) (nonzero : point ≠ 0) :
    Function.Injective (fun scalar : ScalarField => scalarMultiplication scalar point) := by
  exact smul_left_injective ScalarField nonzero

/-- An output-based mathematical inverse. This does not supply an efficient algorithm. -/
noncomputable def recover (input : AffineInput) (output : Option Point) : ScalarField :=
  if existsScalar : ∃ scalar, checkedScalarMultiplication scalar input = output
  then Classical.choose existsScalar else 0

theorem recover_correct (scalar : ScalarField) (input : AffineInput)
    (valid : OnCurve input) :
    recover input (checkedScalarMultiplication scalar input) = scalar := by
  classical
  have existsScalar : ∃ r, checkedScalarMultiplication r input =
      checkedScalarMultiplication scalar input := ⟨scalar, rfl⟩
  have selected := Classical.choose_spec existsScalar
  obtain ⟨point, decoded⟩ := Option.ne_none_iff_exists'.mp ((decodePoint_defined input).mpr valid)
  apply scalar_injective point (decodePoint_ne_zero input point decoded)
  have same : scalarMultiplication (Classical.choose existsScalar) point =
      scalarMultiplication scalar point := by
    simpa [checkedScalarMultiplication, decoded] using selected
  simpa [recover, dif_pos existsScalar] using same

end Kriterion.ScalarRecovery
