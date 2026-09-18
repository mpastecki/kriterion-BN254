import Construction.TruncatedBiquadratic
import Construction.TruncatedPointEncoding

namespace Kriterion.ArgoMAC.TruncatedPointSchema

open BN254

private def packRows
    (x9 y6 y8 y10 : Vector TruncatedBitAdaptor.Table coordinateBitCount)
    (yx7 yx9 yy8 : Vector TruncatedBitAdaptor.Table coordinateBitCount)
    (zx7 zx9 zy6 zy8 zy10 : Vector TruncatedBitAdaptor.Table coordinateBitCount) :
    Fin 3048 → BitVec 254 := fun index =>
  let location := (finProdFinEquiv : Fin 12 × Fin coordinateBitCount ≃ Fin 3048).symm index
  let rows := #v[x9, y6, y8, y10, yx7, yx9, yy8, zx7, zx9, zy6, zy8, zy10]
  ((rows.get location.1).get location.2).trueRow

/-- This accepts only the X4/Y3/Z5 generated layout.
All other optional layouts use the universal fallback codec. -/
def generated? (x y z : TruncatedBiquadratic.Table) :
    Option TruncatedPointEncoding.GeneratedTriple :=
  match x.c0, x.c1, x.c2, x.c3, x.c4, x.c5, x.x7, x.x9, x.y6, x.y8, x.y10,
    y.c0, y.c1, y.c2, y.c3, y.c4, y.c5, y.x7, y.x9, y.y6, y.y8, y.y10,
    z.c0, z.c1, z.c2, z.c3, z.c4, z.c5, z.x7, z.x9, z.y6, z.y8, z.y10 with
  | some xc0, some xc1, some xc2, some xc3, none, some xc5,
      none, some xx9, some xy6, some xy8, some xy10,
      some yc0, some yc1, none, none, some yc4, some yc5,
      some yx7, some yx9, none, some yy8, none,
      some zc0, none, some zc2, some zc3, some zc4, some zc5,
      some zx7, some zx9, some zy6, some zy8, some zy10 =>
    some {
      coefficients := #v[xc0, xc1, xc2, xc3, xc5,
        yc0, yc1, yc4, yc5, zc0, zc2, zc3, zc4, zc5].get
      rows := packRows xx9 xy6 xy8 xy10 yx7 yx9 yy8 zx7 zx9 zy6 zy8 zy10
    }
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => none

private def unpackRows (packed : Fin 3048 → BitVec 254) (kind : Fin 12) :
    Vector TruncatedBitAdaptor.Table coordinateBitCount :=
  Vector.ofFn fun position => ⟨packed (finProdFinEquiv (kind, position))⟩

private theorem unpack_pack
    (x9 y6 y8 y10 yx7 yx9 yy8 zx7 zx9 zy6 zy8 zy10 :
      Vector TruncatedBitAdaptor.Table coordinateBitCount) (kind : Fin 12) :
    unpackRows (packRows x9 y6 y8 y10 yx7 yx9 yy8 zx7 zx9 zy6 zy8 zy10) kind =
      (#v[x9, y6, y8, y10, yx7, yx9, yy8, zx7, zx9, zy6, zy8, zy10]).get kind := by
  apply Vector.ext
  intro index inRange
  simp only [unpackRows, packRows, Vector.getElem_ofFn, Equiv.symm_apply_apply]
  rfl

/-- The three tables of the generated X4/Y3/Z5 layout. -/
def tablesOf (value : TruncatedPointEncoding.GeneratedTriple) :
    TruncatedBiquadratic.Table × TruncatedBiquadratic.Table × TruncatedBiquadratic.Table :=
  let c := value.coefficients
  let r := unpackRows value.rows
  ( { c0 := some (c 0), c1 := some (c 1), c2 := some (c 2), c3 := some (c 3), c4 := none,
      c5 := some (c 4), x7 := none, x9 := some (r 0), y6 := some (r 1), y8 := some (r 2),
      y10 := some (r 3) },
    { c0 := some (c 5), c1 := some (c 6), c2 := none, c3 := none, c4 := some (c 7),
      c5 := some (c 8), x7 := some (r 4), x9 := some (r 5), y6 := none, y8 := some (r 6),
      y10 := none },
    { c0 := some (c 9), c1 := none, c2 := some (c 10), c3 := some (c 11), c4 := some (c 12),
      c5 := some (c 13), x7 := some (r 7), x9 := some (r 8), y6 := some (r 9), y8 := some (r 10),
      y10 := some (r 11) } )

theorem tablesOf_generated (x y z : TruncatedBiquadratic.Table)
    (value : TruncatedPointEncoding.GeneratedTriple) (encoded : generated? x y z = some value) :
    tablesOf value = (x, y, z) := by
  rcases x with ⟨xc0, xc1, xc2, xc3, xc4, xc5, xx7, xx9, xy6, xy8, xy10⟩
  rcases y with ⟨yc0, yc1, yc2, yc3, yc4, yc5, yx7, yx9, yy6, yy8, yy10⟩
  rcases z with ⟨zc0, zc1, zc2, zc3, zc4, zc5, zx7, zx9, zy6, zy8, zy10⟩
  unfold generated? at encoded
  split at encoded
  · injection encoded with encoded
    subst value
    simp_all [tablesOf, unpack_pack]
  · simp_all

end Kriterion.ArgoMAC.TruncatedPointSchema
