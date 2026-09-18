import Construction.ArgoMAC.BitAdaptor

namespace Kriterion.ArgoMAC.TruncatedBitAdaptor

open BN254 Cryptography

abbrev Row := BitVec 254

def truncate (value : BitAdaptor.Ciphertext) : Row := value.extractLsb' 0 254

def padRow (permutations : BitAdaptor.FixedKeyPermutations) (label : Block) : Row :=
  truncate (BitAdaptor.padBytes permutations label)

def fieldRow (value : BaseField) : Row :=
  truncate (BitAdaptor.fieldBytes value)

def encrypt (permutations : BitAdaptor.FixedKeyPermutations) (label : Block)
    (message : BaseField) : Row :=
  padRow permutations label ^^^ fieldRow message

def decrypt (permutations : BitAdaptor.FixedKeyPermutations) (label : Block)
    (ciphertext : Row) : BaseField :=
  (padRow permutations label ^^^ ciphertext).toNat

structure Table where
  trueRow : Row

def garble (permutations : BitAdaptor.FixedKeyPermutations) (slope : BaseField)
    (key : BitAdaptor.Key) : Table × BitAdaptor.OutputKey :=
  let outputKey : BitAdaptor.OutputKey := {
    slope
    offset := (BitAdaptor.hashBytes permutations key.falseLabel).toNat
  }
  ({ trueRow := encrypt permutations key.trueLabel (outputKey.encode true) }, outputKey)

def evaluate (permutations : BitAdaptor.FixedKeyPermutations) (table : Table)
    (value : Bool) (input : Block) : BaseField :=
  if value then decrypt permutations input table.trueRow
  else (BitAdaptor.hashBytes permutations input).toNat

end Kriterion.ArgoMAC.TruncatedBitAdaptor
