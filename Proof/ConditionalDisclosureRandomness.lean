import Construction.ConditionalDisclosure
import Proof.Privacy.Distribution.Distribution

namespace Kriterion.ConditionalDisclosure.Randomness

open BN254 Cryptography ArgoMAC ArgoMAC.Security
noncomputable section

/-- All curve coefficients, selected-label keys, and every public evaluation oracle. -/
abbrev CurveRandomness := GarblingFieldData × GarblingOracleData

/-- The discarded factor retains its original universally quantified clamping proof. -/
abbrev UnusedPointRandomness :=
  {point : GarblingPointData // ∀ [FieldCertificate] [GroupCertificate], point.offsets.IsClamped}

instance unusedPointFintype : Fintype UnusedPointRandomness := Fintype.ofFinite _

def project (tape : Garbling.Randomness) : CurveRandomness :=
  ((Garbling.Randomness.data tape).algebraic.field, (Garbling.Randomness.data tape).oracles)

/-- This is a literal product split, with no ignored proof or restriction. -/
def splitEquiv : Garbling.Randomness ≃ CurveRandomness × UnusedPointRandomness where
  toFun tape := (project tape, ⟨(Garbling.Randomness.data tape).algebraic.point, tape.offsetsClamped⟩)
  invFun sample := {
    offsets := sample.2.1.offsets
    offsetsClamped := sample.2.2
    pointRandomness := sample.2.1.pointRandomness
    bridgeKey := sample.1.1.bridgeKey
    curveMask := sample.1.1.curveMask
    curveR1 := sample.1.1.curveR1
    curveR2 := sample.1.1.curveR2
    fixedKeyOracle := sample.1.2.fixedKeyOracle
    inputMacKey := sample.1.2.inputMacKey
    encPRFOracle := sample.1.2.encPRFOracle
    hashOracle := sample.1.2.hashOracle }
  left_inv tape := by cases tape; rfl
  right_inv sample := by
    rcases sample with ⟨⟨field, oracles⟩, ⟨point, proof⟩⟩
    cases field
    cases oracles
    cases point
    rfl

/-- The unchanged complete security tape has exactly the uniform curve/oracle marginal. -/
theorem project_uniform (witness : Garbling.Randomness) (parameter : Nat) :
    letI : Nonempty CurveRandomness := ⟨project witness⟩
    (randomTape witness parameter).map project = PMF.uniformOfFintype CurveRandomness := by
  letI : Nonempty Garbling.Randomness := ⟨witness⟩
  letI : Nonempty CurveRandomness := ⟨project witness⟩
  letI : Nonempty UnusedPointRandomness := ⟨(splitEquiv witness).2⟩
  change (PMF.uniformOfFintype Garbling.Randomness).map project = _
  calc
    _ = ((PMF.uniformOfFintype Garbling.Randomness).map splitEquiv).map Prod.fst := by
      rw [PMF.map_comp]
      rfl
    _ = (PMF.uniformOfFintype (CurveRandomness × UnusedPointRandomness)).map Prod.fst := by
      rw [uniform_map_equiv]
    _ = _ := uniform_map_fst

/-- The conditional disclosure garbler consumes exactly the projected data. -/
def garbleProjected (scalar : ScalarField) (sample : CurveRandomness) : Public := {
  curve := CurveMembership.garble sample.1.bridgeKey sample.1.curveMask.value
    sample.1.curveR1 sample.1.curveR2
    (Pipeline.curveOracles sample.2.fixedKeyOracle) sample.2.inputMacKey
  scalarCiphertext := encrypt sample.2.hashOracle sample.1.bridgeKey scalar }

theorem garble_project (scalar : ScalarField) (tape : Garbling.Randomness) :
    garble scalar tape = garbleProjected scalar (project tape) := rfl

end
end Kriterion.ConditionalDisclosure.Randomness
