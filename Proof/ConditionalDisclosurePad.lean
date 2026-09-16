import Proof.ConditionalDisclosureHash

namespace Kriterion.ConditionalDisclosure.Hash

/-- Swap a fresh hash reply with a private pad, applying the scalar-mask translation. -/
def swapSource (prior : List (BN254.BaseField × Pair)) (bridge : BN254.BaseField)
    (shift : Pair) (fresh : Fresh prior bridge) (source : Fiber prior × Pair) :
    Fiber prior × Pair :=
  (⟨Function.update source.1.1 bridge (translate shift source.2), by
    intro entry member
    rw [Function.update_of_ne (fresh entry member)]
    exact source.1.2 entry member⟩,
    translate shift (source.1.1 bridge))

theorem swapSource_twice (prior : List (BN254.BaseField × Pair)) (bridge : BN254.BaseField)
    (shift : Pair) (fresh : Fresh prior bridge) (source : Fiber prior × Pair) :
    swapSource prior bridge shift fresh (swapSource prior bridge shift fresh source) = source := by
  apply Prod.ext
  · apply Subtype.ext
    funext input
    by_cases equal : input = bridge
    · subst input
      simp [swapSource, translate_twice]
    · simp [swapSource, Function.update_of_ne equal]
  · simp [swapSource, translate_twice]

def sourceEquiv (prior : List (BN254.BaseField × Pair)) (bridge : BN254.BaseField)
    (shift : Pair) (fresh : Fresh prior bridge) : (Fiber prior × Pair) ≃ (Fiber prior × Pair) where
  toFun := swapSource prior bridge shift fresh
  invFun := swapSource prior bridge shift fresh
  left_inv := swapSource_twice prior bridge shift fresh
  right_inv := swapSource_twice prior bridge shift fresh

def realObservation (prior : List (BN254.BaseField × Pair)) (bridge : BN254.BaseField)
    (shift : Pair) (source : Fiber prior × Pair) : ArgoMAC.EncPRF.HashOracle × Pair :=
  (source.1.1, translate shift (source.1.1 bridge))

def simulatedObservation (prior : List (BN254.BaseField × Pair)) (bridge : BN254.BaseField)
    (shift : Pair) (source : Fiber prior × Pair) : ArgoMAC.EncPRF.HashOracle × Pair :=
  (Function.update source.1.1 bridge (translate shift source.2), source.2)

theorem observation_swap (prior : List (BN254.BaseField × Pair)) (bridge : BN254.BaseField)
    (shift : Pair) (fresh : Fresh prior bridge) (source : Fiber prior × Pair) :
    realObservation prior bridge shift (sourceEquiv prior bridge shift fresh source) =
      simulatedObservation prior bridge shift source := by
  simp [realObservation, simulatedObservation, sourceEquiv, swapSource, translate_twice]

/-- Exact coupling at a fixed fresh bridge, conditional on the complete prior hash replies.
Adaptive selection and its probability weights are obligations for the calling game proof. -/
theorem pad_coupling (prior : List (BN254.BaseField × Pair)) (bridge : BN254.BaseField)
    (shift : Pair) (fresh : Fresh prior bridge)
    [Fintype (Fiber prior)] [Nonempty (Fiber prior)] :
    (PMF.uniformOfFintype (Fiber prior × Pair)).map (realObservation prior bridge shift) =
      (PMF.uniformOfFintype (Fiber prior × Pair)).map
        (simulatedObservation prior bridge shift) := by
  have uniform := PMF.uniformOfFintype_map_of_bijective
    (sourceEquiv prior bridge shift fresh) (sourceEquiv prior bridge shift fresh).bijective
  calc
    _ = ((PMF.uniformOfFintype (Fiber prior × Pair)).map
        (sourceEquiv prior bridge shift fresh)).map (realObservation prior bridge shift) := by
      rw [uniform]
    _ = _ := by
      rw [PMF.map_comp]
      apply congrArg (fun f => (PMF.uniformOfFintype (Fiber prior × Pair)).map f)
      funext source
      exact observation_swap prior bridge shift fresh source

end Kriterion.ConditionalDisclosure.Hash
