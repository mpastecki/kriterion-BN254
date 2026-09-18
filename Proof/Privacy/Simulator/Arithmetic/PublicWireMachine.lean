import Proof.Privacy.Simulator.Arithmetic.PublicWire

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol Security

/-- A digit contains exactly 254 full-word segments. -/
@[simp] theorem wireDigit_length (base : Nat) : (wireDigit base).length = 254 := by
  simp [wireDigit]

/-- The curve wire contains three coefficients and five digit tables. -/
@[simp] theorem publicCurveWire_length : publicCurveWire.length = 1273 := by
  simp [publicCurveWire]

@[simp] theorem publicXWire_length (row : Nat) : (publicXWire row).length = 1032 := by
  simp [publicXWire, wireCoefficient, wireOptionalDigit]

@[simp] theorem publicYWire_length (row : Nat) : (publicYWire row).length = 1031 := by
  simp [publicYWire, wireCoefficient, wireOptionalDigit]

@[simp] theorem publicZWire_length (row : Nat) : (publicZWire row).length = 1286 := by
  simp [publicZWire, wireCoefficient, wireOptionalDigit]

/-- The complete public wire has exactly 309381 fixed segments. -/
theorem publicWire_length : publicWire.length = 309381 := by
  simp [publicWire, List.length_flatMap]

attribute [local irreducible] publicWire wireSegmentsProgram

/-- The fixed serializer table fits the machine's address space. -/
theorem publicWire_fits : (wireSegmentsProgram publicWire).length < 2 ^ 256 := by
  have bound := wireSegments_length publicWire
  rw [publicWire_length] at bound
  exact lt_of_le_of_lt bound (by decide)

/-- The checked package keeps the large fixed program symbolic during type checking. -/
private opaque publicWireProgramPackage :
    {program : List LinearInstruction // program = wireSegmentsProgram publicWire} :=
  ⟨wireSegmentsProgram publicWire, rfl⟩

def publicWireProgram : List LinearInstruction := publicWireProgramPackage.val

theorem publicWireProgram_eq : publicWireProgram = wireSegmentsProgram publicWire :=
  publicWireProgramPackage.property

theorem publicWireProgram_fits : publicWireProgram.length < 2 ^ 256 := by
  rw [publicWireProgram_eq]
  exact publicWire_fits

/-- The serializer contains only fixed loads, arithmetic instructions, and bit writes. -/
def publicWireMachine : Machine := linearMachine publicWireProgram publicWireProgram_fits

/-- The serializer returns the complete canonical public wire and retains source RAM. -/
theorem publicWireMachine_run [FieldCertificate] (coin : SimulatorSampling.OfflineCoin)
    (memory : Memory) (stored : WordsAt memory.ram (memory.registers 11) 0 (offlineSchedule.words coin)) :
    (run publicWireMachine (publicWireProgram.length + 1)
      ⟨⟨0, Nat.zero_lt_succ publicWireMachine.size⟩, memory⟩).map
      (Option.map fun result => (result.1.memory.bits 3, result.1.memory.ram, result.2)) =
      PMF.pure (some ((Wire.encoding.encode (publicSourceTable coin.1)).flatMap (fun byte => bits 8 byte.val) ++
        memory.bits 3, memory.ram, publicWireProgram.length + 1)) := by
  have bits := wireSegments_bits publicWire memory
  have saved := (wireSegments_preserves publicWire memory).1
  rw [← publicWireProgram_eq] at bits saved
  rw [publicWire_bits coin.1 memory.ram (memory.registers 11) (offline_public_words coin _ _ stored)] at bits
  unfold publicWireMachine
  rw [linearMachine_run, PMF.pure_map]
  simp only [Option.map_some, bits, Function.update_self, saved]

/-- The complete serializer pays for its table and all executed instructions. -/
theorem publicWireMachine_budget :
    publicWireMachine.size + 1 + (publicWireProgram.length + 1) ≤ 477065504 := by
  have bound : publicWireProgram.length ≤ 771 * publicWire.length := by
    rw [publicWireProgram_eq]
    exact wireSegments_length publicWire
  rw [publicWire_length] at bound
  change publicWireProgram.length + 1 + (publicWireProgram.length + 1) ≤ _
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
