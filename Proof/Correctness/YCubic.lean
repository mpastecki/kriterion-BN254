import Construction.ArgoMAC.Cubic

namespace Kriterion.ArgoMAC.Cubic

open BN254

/-- The mask cancellation holds for every input and every offset. -/
theorem cancellation (coefficients : Coefficients) (randomness : Randomness)
    (highOffset middleOffset lowOffset x : BaseField) :
    polynomial ⟨coefficients.c0 - lowOffset, coefficients.c1 + randomness.r1,
        coefficients.c2 + randomness.r2, coefficients.c3 + randomness.r3⟩ x +
      (-randomness.r3 * x + highOffset) * x ^ 2 +
      (-(randomness.r2 + highOffset) * x + middleOffset) * x +
      (-(randomness.r1 + middleOffset) * x + lowOffset) = polynomial coefficients x := by
  simp only [polynomial]
  ring

/-- Correct labels evaluate the cubic for every oracle, tape, and field input. -/
theorem evaluateEncoded (coefficients : Coefficients) (randomness : Randomness)
    (oracles : Oracles) (key : CoordinateMacKey) (x : BaseField) :
    evaluate oracles (garble coefficients randomness oracles key) x
      (encodeCoordinate key (coordinateBits x)) = polynomial coefficients x := by
  simp only [evaluate, garble]
  rw [CurveMembership.evaluateDigitGarbleEncode,
    CurveMembership.evaluateDigitGarbleEncode, CurveMembership.evaluateDigitGarbleEncode]
  exact cancellation coefficients randomness _ _ _ x

/-- The represented polynomial differs from the RCB row by a curve-equation multiple. -/
theorem fromY_residual (row : Coordinates.Coefficients) (input : AffineInput)
    (noY : row.y = 0) (noXY : row.xy = 0) :
    polynomial (fromY row) input.x - Coordinates.evaluate row input =
      row.ySquared * (input.x ^ 3 + 3 - input.y ^ 2) := by
  simp only [polynomial, fromY, Coordinates.evaluate, noY, noXY]
  ring

/-- The curve premise is used only to identify the represented output. -/
theorem fromY_onCurve (row : Coordinates.Coefficients) (input : AffineInput)
    (noY : row.y = 0) (noXY : row.xy = 0) (onCurve : OnCurve input) :
    polynomial (fromY row) input.x = Coordinates.evaluate row input := by
  have residual := fromY_residual row input noY noXY
  rw [show input.x ^ 3 + 3 - input.y ^ 2 = 0 from sub_eq_zero.mpr onCurve.symm,
    mul_zero] at residual
  exact sub_eq_zero.mp residual

/-- RCB Y evaluation keeps its complete homogeneous coordinate. -/
theorem rcbY_onCurve (offset input : AffineInput) (onCurve : OnCurve input) :
    polynomial (fromY (Coordinates.yCoefficients offset)) input.x =
      Coordinates.algorithmY offset input := by
  rw [fromY_onCurve _ input rfl rfl onCurve, Coordinates.evaluateY]

/-- The zero digit and every homogeneous randomizer obey the same rewrite. -/
theorem scaledY_onCurve (offset input : AffineInput) (endomorphism : Option BaseField)
    (randomizer : BaseField) (onCurve : OnCurve input) :
    polynomial (fromY (Coordinates.rows offset endomorphism randomizer).y) input.x =
      Coordinates.evaluate (Coordinates.rows offset endomorphism randomizer).y input := by
  apply fromY_onCurve _ input _ _ onCurve
  · cases endomorphism <;> simp [Coordinates.rows, Coordinates.scale, Coordinates.yCoefficients]
  · cases endomorphism <;> simp [Coordinates.rows, Coordinates.scale, Coordinates.yCoefficients]

end Kriterion.ArgoMAC.Cubic
