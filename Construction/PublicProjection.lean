import GarbledCircuit

namespace Kriterion.PublicProjection

/-- A new public representation leaves the secret encoding key and labels unchanged.
Its evaluator must be justified separately for correctness. -/
def scheme {Circuit Input Output Randomness Public NewPublic Key Labels Oracle : Type}
    (original : GarbledCircuit Circuit Input Output Randomness Public Key Labels Oracle)
    (project : Public → NewPublic)
    (evaluate : Oracle → NewPublic → Input → Labels → Option Output) :
    GarbledCircuit Circuit Input Output Randomness NewPublic Key Labels Oracle where
  function := original.function
  garble parameter circuit randomness :=
    let result := original.garble parameter circuit randomness
    (project result.1, result.2)
  encode := original.encode
  evaluate := evaluate

/-- Public projection preserves the exact existing label-selection interface. -/
def lamportCompatibility {Circuit Input Output Randomness Public NewPublic Key Oracle : Type}
    (original : GarbledCircuit Circuit Input Output Randomness Public Key GarbledCircuit.LamportSignature Oracle)
    (project : Public → NewPublic)
    (evaluate : Oracle → NewPublic → Input → GarbledCircuit.LamportSignature → Option Output)
    (bits : Input → BitVec 508)
    (compatible : GarbledCircuit.LamportCompatibility original bits) :
    GarbledCircuit.LamportCompatibility (scheme original project evaluate) bits where
  keyPairs := compatible.keyPairs
  encodeSelectsLabels := compatible.encodeSelectsLabels

end Kriterion.PublicProjection
