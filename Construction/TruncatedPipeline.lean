import Construction.TruncatedCurveMembership
import Construction.TruncatedFieldMacToECMac

namespace Kriterion.ArgoMAC.TruncatedPipeline

open BN254 Cryptography

structure Table where
  curve : TruncatedCurveMembership.Table
  pointMAC : TruncatedFieldMacToECMac.Table

def project (table : Pipeline.Table) : Table := {
  curve := TruncatedCurveMembership.project table.curve
  pointMAC := TruncatedFieldMacToECMac.project table.pointMAC
}

def evaluate [FieldCertificate]
    (fixedKeyOracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (encPRFOracle : PermutationOracle EncPRF.PermutationIndex Block)
    (hashOracle : EncPRF.HashOracle) (table : Table)
    (input : BitInput) (inputMac : InputMac) : Option FieldMacToECMac.Result :=
  let affineInput := input.toAffine
  match decodePoint affineInput with
  | none => none
  | some _ =>
      let bridgeKey := TruncatedCurveMembership.evaluate fixedKeyOracle table.curve affineInput inputMac
      let pointInputMac := EncPRF.transformMac encPRFOracle
        (EncPRF.whiteningKeys hashOracle bridgeKey) input inputMac
      some (TruncatedFieldMacToECMac.evaluate table.pointMAC
        (TruncatedFieldMacToECMac.pointOracles fixedKeyOracle) affineInput pointInputMac)

end Kriterion.ArgoMAC.TruncatedPipeline
