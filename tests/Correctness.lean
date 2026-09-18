import Proof

open Kriterion Kriterion.BN254

theorem argoMACRandomizedEncodingCorrect [FieldCertificate] [GroupCertificate] :
    RandomizedEncoding.Correctness ArgoMAC.construction.randomizedEncoding :=
  ArgoMAC.construction.randomizedEncodingCorrect

theorem argoMACRandomizedEncodingPrivate [FieldCertificate] [GroupCertificate] :
    RandomizedEncoding.Privacy ArgoMAC.construction.randomizedEncoding
      ArgoMAC.construction.randomizedEncodingSimulator :=
  ArgoMAC.construction.randomizedEncodingPrivate

theorem argoMACOutputCount [FieldCertificate] [GroupCertificate]
    (scalar : ScalarField)
    (randomness : ArgoMAC.OffsetRandomness) (point : Point) :
    (ArgoMAC.construction.outputs scalar randomness point).length = 92 :=
  ArgoMAC.construction.outputCount scalar randomness point

theorem argoMACPerfectCorrectness [FieldCertificate] [GroupCertificate]
    [ArgoMAC.TerminationCertificate] :
    GarbledCircuit.PerfectCorrectness
      (ArgoMAC.Garbling.garbledCircuit ArgoMAC.construction)
      (fun randomness =>
        (randomness.fixedKeyOracle, randomness.encPRFOracle, randomness.hashOracle)) :=
  ArgoMAC.RCBComplete.perfectCorrectness

def argoMACLamportCompatible [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.LamportCompatibility
      ArgoMAC.Lamport.wireCircuit affineLamportBits :=
  ArgoMAC.Lamport.compatible

theorem seedOffsetsClamped [FieldCertificate] [GroupCertificate] :
    ArgoMAC.Seed.offsets.IsClamped :=
  ArgoMAC.Seed.offsets_clamped

/-- The public circuit uses the three shared slots for every input and tape. -/
theorem argoMACSharedPerfectCorrectness [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.PerfectCorrectness ArgoMAC.Shared.wireCircuit
      ArgoMAC.Shared.evaluationOracle :=
  ArgoMAC.Shared.perfectCorrectness

/-- The public circuit sends exactly 508 selected Lamport labels. -/
def argoMACSharedLamportCompatible [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.LamportCompatibility
      ArgoMAC.Shared.wireCircuit affineLamportBits :=
  ArgoMAC.Shared.lamportCompatible

/-- The public bytes have the same length for every scalar and tape. -/
theorem argoMACSharedCiphertextSize [FieldCertificate] [GroupCertificate]
    (parameter : Nat) (scalar : NonZeroScalar) (tape : ArgoMAC.Shared.Randomness) :
    (ArgoMAC.Wire.encoding.encode
      (ArgoMAC.Shared.wireCircuit.garble parameter scalar tape).1).length = 9806076 :=
  ArgoMAC.Shared.ciphertextSize parameter scalar tape
