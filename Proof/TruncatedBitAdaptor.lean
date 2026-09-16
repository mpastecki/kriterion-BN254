import Construction.TruncatedBitAdaptor

namespace Kriterion.ArgoMAC.TruncatedBitAdaptor

open BN254 Cryptography

theorem decrypt_encrypt (permutations : BitAdaptor.FixedKeyPermutations) (label : Block)
    (message : BaseField) :
    decrypt permutations label (encrypt permutations label message) = message := by
  unfold decrypt encrypt fieldRow padRow truncate
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  simp only [BitVec.extractLsb'_toNat, BitAdaptor.fieldBytes, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (lt_trans message.val_lt (by decide : baseFieldModulus < 2 ^ 256))]
  simp only [Nat.shiftRight_zero]
  rw [Nat.mod_eq_of_lt (lt_trans message.val_lt (by decide : baseFieldModulus < 2 ^ 254))]
  exact ZMod.natCast_zmod_val message

theorem evaluate_garble (permutations : BitAdaptor.FixedKeyPermutations) (slope : BaseField)
    (key : BitAdaptor.Key) (value : Bool) :
    evaluate permutations (garble permutations slope key).1 value (BitAdaptor.encode key value) =
      (garble permutations slope key).2.encode value := by
  cases value <;> simp [evaluate, garble, BitAdaptor.encode, BitAdaptor.OutputKey.encode]
  exact decrypt_encrypt permutations key.trueLabel (slope + (BitAdaptor.hashBytes permutations key.falseLabel).toNat)

theorem evaluate_projected_garble (permutations : BitAdaptor.FixedKeyPermutations)
    (slope : BaseField) (key : BitAdaptor.Key) (value : Bool) :
    evaluate permutations
      { trueRow := truncate ((BitAdaptor.garble (BitAdaptor.fixedKeyOracle permutations) slope key).1).trueRow }
      value (BitAdaptor.encode key value) =
      (BitAdaptor.garble (BitAdaptor.fixedKeyOracle permutations) slope key).2.encode value := by
  cases value <;> simp [evaluate, BitAdaptor.garble, BitAdaptor.fixedKeyOracle,
    BitAdaptor.encode, BitAdaptor.OutputKey.encode]
  unfold truncate
  rw [BitVec.extractLsb'_xor]
  simpa [encrypt, padRow, fieldRow, truncate] using
    decrypt_encrypt permutations key.trueLabel (slope + (BitAdaptor.hashBytes permutations key.falseLabel).toNat)

end Kriterion.ArgoMAC.TruncatedBitAdaptor
