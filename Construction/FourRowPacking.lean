import Construction.BitRowPacking

namespace Kriterion.FourRowPacking

/-- Four 254-bit rows occupy exactly 127 bytes. All arithmetic is block-local. -/
def block : Encoding (Fin 4 → BitVec 254) :=
  BitRowPacking.encoding 254 4 127 (by decide)

theorem block_length (value : Fin 4 → BitVec 254) :
    (block.encode value).length = 127 :=
  BitRowPacking.encoding_length 254 4 127 _ value

def chunk (groups : Nat) (value : Fin (groups * 4) → BitVec 254) :
    Vector (Fin 4 → BitVec 254) groups :=
  Vector.ofFn fun group position => value (finProdFinEquiv (group, position))

def unchunk (groups : Nat) (value : Vector (Fin 4 → BitVec 254) groups) :
    Fin (groups * 4) → BitVec 254 := fun index =>
  let location := (finProdFinEquiv : Fin groups × Fin 4 ≃ Fin (groups * 4)).symm index
  value[location.1.val] location.2

theorem unchunk_chunk (groups : Nat) (value : Fin (groups * 4) → BitVec 254) :
    unchunk groups (chunk groups value) = value := by
  funext index
  simp only [unchunk, chunk, Vector.getElem_ofFn]
  exact congrArg value (Equiv.apply_symm_apply finProdFinEquiv index)

/-- Universal complete encoding; decoding also preserves arbitrary trailing bytes. -/
def encoding (groups : Nat) : Encoding (Fin (groups * 4) → BitVec 254) :=
  (Encoding.vector block groups).map (chunk groups) (unchunk groups)
    (unchunk_chunk groups)

theorem encoding_length (groups : Nat) (value : Fin (groups * 4) → BitVec 254) :
    ((encoding groups).encode value).length = groups * 127 := by
  exact Encoding.vector_length block 127 groups (chunk groups value)
    (fun index => block_length ((chunk groups value).get index))

end Kriterion.FourRowPacking
