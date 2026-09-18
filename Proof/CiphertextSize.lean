import Construction.ArgoMAC.Encoding

namespace Kriterion.ArgoMAC.Wire

open BN254

/-- Every garbling has the declared ciphertext size. -/
theorem ciphertextSize [FieldCertificate] [GroupCertificate]
    (parameter : Nat) (scalar : NonZeroScalar) (randomness : Garbling.Randomness) :
    (encoding.encode
      ((Garbling.garbledCircuit construction).garble parameter scalar randomness).1).length =
      9806076 := by
  dsimp only [Garbling.garbledCircuit]
  have size := garble_length construction scalar randomness
  simpa only [Garbling.PublicCircuit] using size

end Kriterion.ArgoMAC.Wire
