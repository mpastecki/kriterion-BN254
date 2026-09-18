import Construction.TruncatedBiquadratic
import Construction.ArgoMAC.FieldMacToECMac

namespace Kriterion.ArgoMAC.TruncatedFieldMacToECMac

open BN254 Cryptography

structure Table where
  x : Vector TruncatedBiquadratic.Table FieldMacToECMac.outputMacCount
  y : Vector TruncatedBiquadratic.Table FieldMacToECMac.outputMacCount
  z : Vector TruncatedBiquadratic.Table FieldMacToECMac.outputMacCount

def project (table : FieldMacToECMac.Table) : Table := {
  x := table.x.map TruncatedBiquadratic.project
  y := table.y.map TruncatedBiquadratic.project
  z := table.z.map TruncatedBiquadratic.project
}

def pointOracles (oracle : PermutationOracle Pipeline.FixedKeyIndex Cryptography.Block) :
    Vector (TruncatedBiquadratic.Oracles × TruncatedBiquadratic.Oracles ×
      TruncatedBiquadratic.Oracles) FieldMacToECMac.outputMacCount :=
  Vector.ofFn fun output =>
    (TruncatedBiquadratic.pointOracles oracle output .x,
      TruncatedBiquadratic.pointOracles oracle output .y,
      TruncatedBiquadratic.pointOracles oracle output .z)

def evaluateHomogeneous (table : Table)
    (oracles : Vector (TruncatedBiquadratic.Oracles × TruncatedBiquadratic.Oracles ×
      TruncatedBiquadratic.Oracles) FieldMacToECMac.outputMacCount)
    (input : AffineInput) (inputMac : InputMac) :
    Vector FieldMacToECMac.HomogeneousValue FieldMacToECMac.outputMacCount :=
  Vector.ofFn fun index => {
    x := TruncatedBiquadratic.evaluate (oracles.get index).1 (table.x.get index) input inputMac
    y := TruncatedBiquadratic.evaluateY (oracles.get index).2.1 (table.y.get index) input inputMac
    z := TruncatedBiquadratic.evaluate (oracles.get index).2.2 (table.z.get index) input inputMac
  }

def evaluate (table : Table)
    (oracles : Vector (TruncatedBiquadratic.Oracles × TruncatedBiquadratic.Oracles ×
      TruncatedBiquadratic.Oracles) FieldMacToECMac.outputMacCount)
    (input : AffineInput) (inputMac : InputMac) : FieldMacToECMac.Result := {
  point := input
  pointMacs := evaluateHomogeneous table oracles input inputMac
}

end Kriterion.ArgoMAC.TruncatedFieldMacToECMac
