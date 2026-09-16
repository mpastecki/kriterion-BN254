import Construction.TruncatedDirectDisclosure
import Proof.PublicProjection
import Proof.DirectDisclosureSimulator
import Proof.LamportCompatibility.Labels

namespace Kriterion.TruncatedDirectDisclosure
open BN254 ArgoMAC

/-- The old simulator retains its state and publishes only the projected table. -/
noncomputable def simulator [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.Simulator AffineInput (Option Point) Public Garbling.Labels Unit
      DirectDisclosure.Simulation.State :=
  PublicProjection.simulator DirectDisclosure.Simulation.simulator TruncatedCurveMembership.project

theorem oracleSimulation [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.OracleSimulation simulator DirectDisclosure.Simulation.handler
      DirectDisclosure.Simulation.State.view :=
  PublicProjection.oracleSimulation DirectDisclosure.Simulation.simulator TruncatedCurveMembership.project
    DirectDisclosure.Simulation.handler DirectDisclosure.Simulation.State.view DirectDisclosure.Simulation.oracleSimulation

/-- The complete original privacy theorem suffices; no new source or oracle assumption is added. -/
theorem adaptivePrivacy [FieldCertificate] [GroupCertificate] {Aux : Type}
    (randomTape : Nat → PMF Garbling.Randomness)
    (original : GarbledCircuit.ConcreteAdaptivePrivacy (Aux := Aux) DirectDisclosure.internalScheme
      DirectDisclosure.topology DirectDisclosure.Simulation.simulator randomTape Garbling.oracleHandler
      DirectDisclosure.Simulation.handler 100) :
    GarbledCircuit.ConcreteAdaptivePrivacy (Aux := Aux) internalScheme topology simulator randomTape
      Garbling.oracleHandler DirectDisclosure.Simulation.handler 100 :=
  PublicProjection.adaptivePrivacy DirectDisclosure.internalScheme TruncatedCurveMembership.project
    (fun oracle table input labels => some (evaluate oracle table input labels.inputMac))
    DirectDisclosure.topology DirectDisclosure.Simulation.simulator randomTape Garbling.oracleHandler
    DirectDisclosure.Simulation.handler 100 original

def wireLamportCompatible [FieldCertificate] [GroupCertificate] :
    GarbledCircuit.LamportCompatibility wireScheme affineLamportBits := {
  keyPairs := Lamport.keyPairs
  encodeSelectsLabels := fun key input => Lamport.selectedLabels_eq key input
}

theorem ciphertextSize [FieldCertificate] [GroupCertificate]
    (parameter : Nat) (scalar : NonZeroScalar) (tape : Garbling.Randomness) :
    (TruncatedCurveMembership.Wire.encoding.encode (internalScheme.garble parameter scalar tape).1).length = 40419 :=
  TruncatedCurveMembership.Wire.encoding_length _

end Kriterion.TruncatedDirectDisclosure
