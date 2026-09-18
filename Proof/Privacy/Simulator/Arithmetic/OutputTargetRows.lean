import Proof.Privacy.Simulator.Arithmetic.OutputTargetsSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The typed target-row memory uses the original sampled points and scales. -/
def outputTargetRowsMemory [BN254.FieldCertificate] [BN254.GroupCertificate] (base : Memory) (output : BN254.Point)
    (sample : (Fin 91 → BN254.Point) × (Fin 92 → BN254.NonZeroBase)) : Memory :=
  homogeneousRowsMemory (outputTargetPoint output (Vector.ofFn sample.1)) (outputTargetScale sample.2) 91 base

/-- The host converts the typed online sample into all 92 exact output-target rows. -/
theorem outputTargetRowsBlock_run [BN254.FieldCertificate] [BN254.GroupCertificate] (host : Machine)
    (labels : Fin 2302 → Fin (host.size + 1))
    (present : ContainsHomogeneousRows host 91 (by decide) labels) (fuel : Nat) (base : Memory)
    (output : BN254.Point) (sample : (Fin 91 → BN254.Point) × (Fin 92 → BN254.NonZeroBase))
    (encoded : PointAccumulatorEncoding base (output - radix • pointHorner radix (Vector.ofFn sample.1).toList))
    (pointer : base.registers 10 = base.registers 11 + 92)
    (stored : WordsAt base.ram (base.registers 11) 0 (onlineWords sample))
    (separate : HomogeneousRegionsDisjoint base 92) :
    run host (fuel + 2018) ⟨labels 0, base⟩ =
      (run host fuel ⟨labels 2301, outputTargetRowsMemory base output sample⟩).map
        (Option.map fun result => (result.1, result.2 + 2018)) := by
  have pointSource (i : Nat) (inside : i < 92) (positive : i ≠ 0) :
      StoredPointEncoding base.ram (base.registers 10 + BitVec.ofNat 256 (3 * (i - 1)))
        (outputTargetPoint output (Vector.ofFn sample.1) i) := by
    let index : Fin 91 := ⟨i - 1, by omega⟩
    have row := outputTargetPoint_free output (Vector.ofFn sample.1) index
    have same : index.val + 1 = i := by dsimp [index]; omega
    rw [same, Vector.get_ofFn] at row
    rw [row, pointer]
    exact onlineWords_pointEncoding base.ram (base.registers 11) sample stored index
  have scaleSource (i : Nat) (inside : i < 92) :
      base.ram (base.registers 11 + BitVec.ofNat 256 i) = BitVec.ofNat 256 (outputTargetScale sample.2 i).value.val := by
    rw [outputTargetScale_value sample.2 ⟨i, inside⟩]
    exact onlineWords_scale base.ram (base.registers 11) sample stored ⟨i, inside⟩
  exact homogeneousRowsBlock_run host 91 (by decide) labels present
    (outputTargetPoint output (Vector.ofFn sample.1)) (outputTargetScale sample.2) fuel base encoded
    pointSource scaleSource separate

/-- The emitted target RAM equals the original outputTargets source definition. -/
theorem outputTargetRowsMemory_ram [BN254.FieldCertificate] [BN254.GroupCertificate]
    (base : Memory) (output : BN254.Point)
    (sample : (Fin 91 → BN254.Point) × (Fin 92 → BN254.NonZeroBase)) :
    (outputTargetRowsMemory base output sample).ram = storeDrawWords (base.registers 13) 0 base.ram
      (vectorWords homogeneousWords (Security.outputTargets output (Vector.ofFn sample.1) sample.2)) := by
  rw [outputTargetRowsMemory, homogeneousRowsMemory_ram]
  exact congrArg (storeDrawWords (base.registers 13) 0 base.ram) (outputTargets_words output (Vector.ofFn sample.1) sample.2)

/-- The target-row phase preserves every protocol bit stack. -/
theorem outputTargetRowsMemory_bits [BN254.FieldCertificate] [BN254.GroupCertificate]
    (base : Memory) (output : BN254.Point)
    (sample : (Fin 91 → BN254.Point) × (Fin 92 → BN254.NonZeroBase)) :
    (outputTargetRowsMemory base output sample).bits = base.bits :=
  homogeneousRowsMemory_bits _ _ _ _

/-- The target-row phase preserves caller registers except the increment register. -/
theorem outputTargetRowsMemory_caller [BN254.FieldCertificate] [BN254.GroupCertificate]
    (base : Memory) (output : BN254.Point)
    (sample : (Fin 91 → BN254.Point) × (Fin 92 → BN254.NonZeroBase))
    (register : Register) (caller : 9 ≤ register.val) (outside : register ≠ 12) :
    (outputTargetRowsMemory base output sample).registers register = base.registers register :=
  homogeneousRowsMemory_caller _ _ _ _ register caller outside

end Kriterion.ArgoMAC.ArithmeticSimulator
