import Construction.ArgoMAC.EncPRF
import Mathlib.Probability.Distributions.Uniform

namespace Kriterion.ConditionalDisclosure.Hash

open BN254 Cryptography ArgoMAC

abbrev Pair := Block × Block

/-- Translation uses both hash blocks. -/
def translate (shift value : Pair) : Pair :=
  (shift.1 ^^^ value.1, shift.2 ^^^ value.2)

theorem translate_twice (shift value : Pair) :
    translate shift (translate shift value) = value := by
  apply Prod.ext <;> simp [translate, ← BitVec.xor_assoc]

/-- Only one hash input changes. -/
def change (bridge : BaseField) (shift : Pair) (oracle : EncPRF.HashOracle) :
    EncPRF.HashOracle :=
  Function.update oracle bridge (translate shift (oracle bridge))

theorem change_other (bridge input : BaseField) (shift : Pair)
    (oracle : EncPRF.HashOracle) (different : input ≠ bridge) :
    change bridge shift oracle input = oracle input := by
  simp [change, different]

theorem change_twice (bridge : BaseField) (shift : Pair) (oracle : EncPRF.HashOracle) :
    change bridge shift (change bridge shift oracle) = oracle := by
  funext input
  by_cases equal : input = bridge
  · subst input
    simp [change, translate_twice]
  · rw [change_other _ _ _ _ equal, change_other _ _ _ _ equal]

def changeEquiv (bridge : BaseField) (shift : Pair) :
    EncPRF.HashOracle ≃ EncPRF.HashOracle where
  toFun := change bridge shift
  invFun := change bridge shift
  left_inv := change_twice bridge shift
  right_inv := change_twice bridge shift

/-- The fiber fixes every previous hash reply. -/
def Compatible (prior : List (BaseField × Pair)) (oracle : EncPRF.HashOracle) : Prop :=
  ∀ entry ∈ prior, oracle entry.1 = entry.2

abbrev Fiber (prior : List (BaseField × Pair)) :=
  {oracle : EncPRF.HashOracle // Compatible prior oracle}

def Fresh (prior : List (BaseField × Pair)) (bridge : BaseField) : Prop :=
  ∀ entry ∈ prior, entry.1 ≠ bridge

theorem change_compatible (prior : List (BaseField × Pair)) (bridge : BaseField)
    (shift : Pair) (fresh : Fresh prior bridge) (oracle : EncPRF.HashOracle)
    (compatible : Compatible prior oracle) :
    Compatible prior (change bridge shift oracle) := by
  intro entry member
  rw [change_other _ _ _ _ (fresh entry member)]
  exact compatible entry member

/-- XOR translation is bijective inside the exact prior-transcript fiber. -/
def fiberEquiv (prior : List (BaseField × Pair)) (bridge : BaseField)
    (shift : Pair) (fresh : Fresh prior bridge) : Fiber prior ≃ Fiber prior where
  toFun oracle := ⟨change bridge shift oracle.1,
    change_compatible prior bridge shift fresh oracle.1 oracle.2⟩
  invFun oracle := ⟨change bridge shift oracle.1,
    change_compatible prior bridge shift fresh oracle.1 oracle.2⟩
  left_inv oracle := Subtype.ext (change_twice bridge shift oracle.1)
  right_inv oracle := Subtype.ext (change_twice bridge shift oracle.1)

theorem fiber_uniform (prior : List (BaseField × Pair)) (bridge : BaseField)
    (shift : Pair) (fresh : Fresh prior bridge)
    [Fintype (Fiber prior)] [Nonempty (Fiber prior)] :
    (PMF.uniformOfFintype (Fiber prior)).map (fiberEquiv prior bridge shift fresh) =
      PMF.uniformOfFintype (Fiber prior) :=
  PMF.uniformOfFintype_map_of_bijective _ (fiberEquiv prior bridge shift fresh).bijective

end Kriterion.ConditionalDisclosure.Hash
