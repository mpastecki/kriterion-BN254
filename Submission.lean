import Solution
import Construction
import Proof

set_option maxRecDepth 4096

namespace Submission
open Kriterion Kriterion.BN254 Kriterion.ArgoMAC

/-- The submission uses 92 digits and three shared permutation slots. -/
def solution : Kriterion.Solution := {
  FixedIndex := Shared.FixedKeyIndex
  EncIndex := EncPRF.PermutationIndex
  fixedFinite := inferInstance
  encFinite := inferInstance
  Randomness := Shared.Randomness
  randomnessFinite := inferInstance
  randomness := Shared.Randomness.ofLegacy (Seed.randomness 0)
  Public := Pipeline.Table
  EncodingKey := Garbling.EncodingKey
  State := Shared.Simulator.State
  encoding := Wire.encoding
  ciphertextBytes := 9806076
  evaluationOracle := Shared.evaluationOracle
  oracleUniform := by
    convert Shared.oracleUniform (Shared.Randomness.ofLegacy (Seed.randomness 0)) using 1
  scheme := fun field group => @Shared.wireCircuit field group
  ciphertextSize := fun field group => @Shared.ciphertextSize field group
  lamportCompatible := fun field group => @Shared.lamportCompatible field group
  idealOracle := Security.circuitSimulatorOracleHandler
  idealView := Security.CircuitSimulatorState.view
  functionCorrect := fun _ _ _ _ => rfl
  perfectCorrectness := fun field group => @Shared.perfectCorrectness field group
  adaptivePrivacy := by
    intro field group
    letI := field
    letI := group
    convert ArithmeticSimulator.compiledAdaptivePrivacy (Aux := Unit)
      (Shared.Randomness.ofLegacy (Seed.randomness 0)) using 1
    rfl
}

end Submission
