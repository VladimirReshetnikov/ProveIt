import PolynomialFormulas.QuinticDummitCoefficients

/-!
# Computable coefficients of Dummit's sextic

A finite sparse table for the seven coefficients, together with a proved
sparse-normalization certificate identifying its evaluation with the six-root
scalar resolvent over every commutative ring.
-/

namespace LeanProofs.PolynomialFormulas.ComputableDummitCoefficients

open QuinticRadicalDecidability
open QuinticRadicalDecidability.MonicQuintic

structure Powers where
  p0 : ℕ
  p1 : ℕ
  p2 : ℕ
  p3 : ℕ
  p4 : ℕ
deriving Repr, DecidableEq

structure SparseTerm where
  coeff : ℤ
  powers : Powers
deriving Repr, DecidableEq

abbrev SparsePolynomial := List SparseTerm

def SparseTerm.eval {R : Type*} [CommRing R]
    (t : SparseTerm) (x : Fin 5 → R) : R :=
  t.coeff * x 0 ^ t.powers.p0 * x 1 ^ t.powers.p1 *
    x 2 ^ t.powers.p2 * x 3 ^ t.powers.p3 * x 4 ^ t.powers.p4

def SparsePolynomial.eval {R : Type*} [CommRing R] :
    SparsePolynomial → (Fin 5 → R) → R
  | [], _ => 0
  | t :: q, x => t.eval x + SparsePolynomial.eval q x

/-- The seven sparse coefficient polynomials, in ascending sextic degree. -/
def dummitTable : Fin 7 → SparsePolynomial :=
  ![
    [
      ⟨16, ⟨8, 0, 2, 0, 2⟩⟩,
      ⟨-8, ⟨8, 0, 1, 2, 1⟩⟩,
      ⟨1, ⟨8, 0, 0, 4, 0⟩⟩,
      ⟨-8, ⟨7, 2, 1, 0, 2⟩⟩,
      ⟨2, ⟨7, 2, 0, 2, 1⟩⟩,
      ⟨-48, ⟨7, 0, 1, 1, 2⟩⟩,
      ⟨12, ⟨7, 0, 0, 3, 1⟩⟩,
      ⟨1, ⟨6, 4, 0, 0, 2⟩⟩,
      ⟨12, ⟨6, 2, 0, 1, 2⟩⟩,
      ⟨-144, ⟨6, 1, 2, 0, 2⟩⟩,
      ⟨88, ⟨6, 1, 1, 2, 1⟩⟩,
      ⟨-13, ⟨6, 1, 0, 4, 0⟩⟩,
      ⟨56, ⟨6, 0, 1, 0, 3⟩⟩,
      ⟨86, ⟨6, 0, 0, 2, 2⟩⟩,
      ⟨72, ⟨5, 3, 1, 0, 2⟩⟩,
      ⟨-22, ⟨5, 3, 0, 2, 1⟩⟩,
      ⟨-4, ⟨5, 2, 2, 1, 1⟩⟩,
      ⟨1, ⟨5, 2, 1, 3, 0⟩⟩,
      ⟨-14, ⟨5, 2, 0, 0, 3⟩⟩,
      ⟨304, ⟨5, 1, 1, 1, 2⟩⟩,
      ⟨-148, ⟨5, 1, 0, 3, 1⟩⟩,
      ⟨152, ⟨5, 0, 3, 0, 2⟩⟩,
      ⟨-54, ⟨5, 0, 2, 2, 1⟩⟩,
      ⟨5, ⟨5, 0, 1, 4, 0⟩⟩,
      ⟨-468, ⟨5, 0, 0, 1, 3⟩⟩,
      ⟨-9, ⟨4, 5, 0, 0, 2⟩⟩,
      ⟨1, ⟨4, 4, 1, 1, 1⟩⟩,
      ⟨-76, ⟨4, 3, 0, 1, 2⟩⟩,
      ⟨370, ⟨4, 2, 2, 0, 2⟩⟩,
      ⟨-287, ⟨4, 2, 1, 2, 1⟩⟩,
      ⟨65, ⟨4, 2, 0, 4, 0⟩⟩,
      ⟨-28, ⟨4, 1, 3, 1, 1⟩⟩,
      ⟨5, ⟨4, 1, 2, 3, 0⟩⟩,
      ⟨-200, ⟨4, 1, 1, 0, 3⟩⟩,
      ⟨-294, ⟨4, 1, 0, 2, 2⟩⟩,
      ⟨8, ⟨4, 0, 5, 0, 1⟩⟩,
      ⟨-2, ⟨4, 0, 4, 2, 0⟩⟩,
      ⟨-676, ⟨4, 0, 2, 1, 2⟩⟩,
      ⟨180, ⟨4, 0, 1, 3, 1⟩⟩,
      ⟨17, ⟨4, 0, 0, 5, 0⟩⟩,
      ⟨625, ⟨4, 0, 0, 0, 4⟩⟩,
      ⟨-210, ⟨3, 4, 1, 0, 2⟩⟩,
      ⟨76, ⟨3, 4, 0, 2, 1⟩⟩,
      ⟨43, ⟨3, 3, 2, 1, 1⟩⟩,
      ⟨-15, ⟨3, 3, 1, 3, 0⟩⟩,
      ⟨50, ⟨3, 3, 0, 0, 3⟩⟩,
      ⟨-6, ⟨3, 2, 4, 0, 1⟩⟩,
      ⟨2, ⟨3, 2, 3, 2, 0⟩⟩,
      ⟨-397, ⟨3, 2, 1, 1, 2⟩⟩,
      ⟨514, ⟨3, 2, 0, 3, 1⟩⟩,
      ⟨-700, ⟨3, 1, 3, 0, 2⟩⟩,
      ⟨447, ⟨3, 1, 2, 2, 1⟩⟩,
      ⟨-118, ⟨3, 1, 1, 4, 0⟩⟩,
      ⟨2300, ⟨3, 1, 0, 1, 3⟩⟩,
      ⟨-12, ⟨3, 0, 4, 1, 1⟩⟩,
      ⟨6, ⟨3, 0, 3, 3, 0⟩⟩,
      ⟨250, ⟨3, 0, 2, 0, 3⟩⟩,
      ⟨1470, ⟨3, 0, 1, 2, 2⟩⟩,
      ⟨-276, ⟨3, 0, 0, 4, 1⟩⟩,
      ⟨27, ⟨2, 6, 0, 0, 2⟩⟩,
      ⟨-9, ⟨2, 5, 1, 1, 1⟩⟩,
      ⟨1, ⟨2, 5, 0, 3, 0⟩⟩,
      ⟨1, ⟨2, 4, 3, 0, 1⟩⟩,
      ⟨141, ⟨2, 4, 0, 1, 2⟩⟩,
      ⟨-185, ⟨2, 3, 2, 0, 2⟩⟩,
      ⟨168, ⟨2, 3, 1, 2, 1⟩⟩,
      ⟨-128, ⟨2, 3, 0, 4, 0⟩⟩,
      ⟨93, ⟨2, 2, 3, 1, 1⟩⟩,
      ⟨19, ⟨2, 2, 2, 3, 0⟩⟩,
      ⟨-125, ⟨2, 2, 1, 0, 3⟩⟩,
      ⟨-610, ⟨2, 2, 0, 2, 2⟩⟩,
      ⟨-36, ⟨2, 1, 5, 0, 1⟩⟩,
      ⟨5, ⟨2, 1, 4, 2, 0⟩⟩,
      ⟨1995, ⟨2, 1, 2, 1, 2⟩⟩,
      ⟨-1174, ⟨2, 1, 1, 3, 1⟩⟩,
      ⟨-16, ⟨2, 1, 0, 5, 0⟩⟩,
      ⟨-3125, ⟨2, 1, 0, 0, 4⟩⟩,
      ⟨375, ⟨2, 0, 4, 0, 2⟩⟩,
      ⟨-172, ⟨2, 0, 3, 2, 1⟩⟩,
      ⟨82, ⟨2, 0, 2, 4, 0⟩⟩,
      ⟨-3500, ⟨2, 0, 1, 1, 3⟩⟩,
      ⟨-1450, ⟨2, 0, 0, 3, 2⟩⟩,
      ⟨198, ⟨1, 5, 1, 0, 2⟩⟩,
      ⟨-78, ⟨1, 5, 0, 2, 1⟩⟩,
      ⟨-95, ⟨1, 4, 2, 1, 1⟩⟩,
      ⟨44, ⟨1, 4, 1, 3, 0⟩⟩,
      ⟨25, ⟨1, 3, 4, 0, 1⟩⟩,
      ⟨-15, ⟨1, 3, 3, 2, 0⟩⟩,
      ⟨15, ⟨1, 3, 1, 1, 2⟩⟩,
      ⟨-384, ⟨1, 3, 0, 3, 1⟩⟩,
      ⟨1, ⟨1, 2, 5, 1, 0⟩⟩,
      ⟨525, ⟨1, 2, 3, 0, 2⟩⟩,
      ⟨-528, ⟨1, 2, 2, 2, 1⟩⟩,
      ⟨384, ⟨1, 2, 1, 4, 0⟩⟩,
      ⟨-1750, ⟨1, 2, 0, 1, 3⟩⟩,
      ⟨-29, ⟨1, 1, 4, 1, 1⟩⟩,
      ⟨-118, ⟨1, 1, 3, 3, 0⟩⟩,
      ⟨625, ⟨1, 1, 2, 0, 3⟩⟩,
      ⟨-850, ⟨1, 1, 1, 2, 2⟩⟩,
      ⟨1760, ⟨1, 1, 0, 4, 1⟩⟩,
      ⟨38, ⟨1, 0, 6, 0, 1⟩⟩,
      ⟨5, ⟨1, 0, 5, 2, 0⟩⟩,
      ⟨-2050, ⟨1, 0, 3, 1, 2⟩⟩,
      ⟨780, ⟨1, 0, 2, 3, 1⟩⟩,
      ⟨-192, ⟨1, 0, 1, 5, 0⟩⟩,
      ⟨3125, ⟨1, 0, 1, 0, 4⟩⟩,
      ⟨7500, ⟨1, 0, 0, 2, 3⟩⟩,
      ⟨-27, ⟨0, 7, 0, 0, 2⟩⟩,
      ⟨18, ⟨0, 6, 1, 1, 1⟩⟩,
      ⟨-4, ⟨0, 6, 0, 3, 0⟩⟩,
      ⟨-4, ⟨0, 5, 3, 0, 1⟩⟩,
      ⟨1, ⟨0, 5, 2, 2, 0⟩⟩,
      ⟨-99, ⟨0, 5, 0, 1, 2⟩⟩,
      ⟨-150, ⟨0, 4, 2, 0, 2⟩⟩,
      ⟨196, ⟨0, 4, 1, 2, 1⟩⟩,
      ⟨48, ⟨0, 4, 0, 4, 0⟩⟩,
      ⟨12, ⟨0, 3, 3, 1, 1⟩⟩,
      ⟨-128, ⟨0, 3, 2, 3, 0⟩⟩,
      ⟨1200, ⟨0, 3, 0, 2, 2⟩⟩,
      ⟨-12, ⟨0, 2, 5, 0, 1⟩⟩,
      ⟨65, ⟨0, 2, 4, 2, 0⟩⟩,
      ⟨-725, ⟨0, 2, 2, 1, 2⟩⟩,
      ⟨-160, ⟨0, 2, 1, 3, 1⟩⟩,
      ⟨-192, ⟨0, 2, 0, 5, 0⟩⟩,
      ⟨3125, ⟨0, 2, 0, 0, 4⟩⟩,
      ⟨-13, ⟨0, 1, 6, 1, 0⟩⟩,
      ⟨-125, ⟨0, 1, 4, 0, 2⟩⟩,
      ⟨590, ⟨0, 1, 3, 2, 1⟩⟩,
      ⟨-16, ⟨0, 1, 2, 4, 0⟩⟩,
      ⟨-1250, ⟨0, 1, 1, 1, 3⟩⟩,
      ⟨-2000, ⟨0, 1, 0, 3, 2⟩⟩,
      ⟨1, ⟨0, 0, 8, 0, 0⟩⟩,
      ⟨-124, ⟨0, 0, 5, 1, 1⟩⟩,
      ⟨17, ⟨0, 0, 4, 3, 0⟩⟩,
      ⟨3250, ⟨0, 0, 2, 2, 2⟩⟩,
      ⟨-1600, ⟨0, 0, 1, 4, 1⟩⟩,
      ⟨256, ⟨0, 0, 0, 6, 0⟩⟩,
      ⟨-9375, ⟨0, 0, 0, 1, 4⟩⟩
    ],
    [
      ⟨-32, ⟨7, 0, 1, 0, 2⟩⟩,
      ⟨8, ⟨7, 0, 0, 2, 1⟩⟩,
      ⟨8, ⟨6, 2, 0, 0, 2⟩⟩,
      ⟨8, ⟨6, 1, 1, 1, 1⟩⟩,
      ⟨-2, ⟨6, 1, 0, 3, 0⟩⟩,
      ⟨48, ⟨6, 0, 0, 1, 2⟩⟩,
      ⟨-2, ⟨5, 3, 0, 1, 1⟩⟩,
      ⟨264, ⟨5, 1, 1, 0, 2⟩⟩,
      ⟨-94, ⟨5, 1, 0, 2, 1⟩⟩,
      ⟨-24, ⟨5, 0, 2, 1, 1⟩⟩,
      ⟨6, ⟨5, 0, 1, 3, 0⟩⟩,
      ⟨-56, ⟨5, 0, 0, 0, 3⟩⟩,
      ⟨-66, ⟨4, 3, 0, 0, 2⟩⟩,
      ⟨-50, ⟨4, 2, 1, 1, 1⟩⟩,
      ⟨19, ⟨4, 2, 0, 3, 0⟩⟩,
      ⟨8, ⟨4, 1, 3, 0, 1⟩⟩,
      ⟨-2, ⟨4, 1, 2, 2, 0⟩⟩,
      ⟨-318, ⟨4, 1, 0, 1, 2⟩⟩,
      ⟨-352, ⟨4, 0, 2, 0, 2⟩⟩,
      ⟨166, ⟨4, 0, 1, 2, 1⟩⟩,
      ⟨3, ⟨4, 0, 0, 4, 0⟩⟩,
      ⟨15, ⟨3, 4, 0, 1, 1⟩⟩,
      ⟨-2, ⟨3, 3, 2, 0, 1⟩⟩,
      ⟨-1, ⟨3, 3, 1, 2, 0⟩⟩,
      ⟨-574, ⟨3, 2, 1, 0, 2⟩⟩,
      ⟨347, ⟨3, 2, 0, 2, 1⟩⟩,
      ⟨194, ⟨3, 1, 2, 1, 1⟩⟩,
      ⟨-89, ⟨3, 1, 1, 3, 0⟩⟩,
      ⟨350, ⟨3, 1, 0, 0, 3⟩⟩,
      ⟨-8, ⟨3, 0, 4, 0, 1⟩⟩,
      ⟨4, ⟨3, 0, 3, 2, 0⟩⟩,
      ⟨1090, ⟨3, 0, 1, 1, 2⟩⟩,
      ⟨-364, ⟨3, 0, 0, 3, 1⟩⟩,
      ⟨162, ⟨2, 4, 0, 0, 2⟩⟩,
      ⟨33, ⟨2, 3, 1, 1, 1⟩⟩,
      ⟨-51, ⟨2, 3, 0, 3, 0⟩⟩,
      ⟨-32, ⟨2, 2, 3, 0, 1⟩⟩,
      ⟨28, ⟨2, 2, 2, 2, 0⟩⟩,
      ⟨305, ⟨2, 2, 0, 1, 2⟩⟩,
      ⟨-2, ⟨2, 1, 4, 1, 0⟩⟩,
      ⟨1340, ⟨2, 1, 2, 0, 2⟩⟩,
      ⟨-901, ⟨2, 1, 1, 2, 1⟩⟩,
      ⟨76, ⟨2, 1, 0, 4, 0⟩⟩,
      ⟨-234, ⟨2, 0, 3, 1, 1⟩⟩,
      ⟨102, ⟨2, 0, 2, 3, 0⟩⟩,
      ⟨-750, ⟨2, 0, 1, 0, 3⟩⟩,
      ⟨-550, ⟨2, 0, 0, 2, 2⟩⟩,
      ⟨-27, ⟨1, 5, 0, 1, 1⟩⟩,
      ⟨9, ⟨1, 4, 2, 0, 1⟩⟩,
      ⟨3, ⟨1, 4, 1, 2, 0⟩⟩,
      ⟨-1, ⟨1, 3, 3, 1, 0⟩⟩,
      ⟨180, ⟨1, 3, 1, 0, 2⟩⟩,
      ⟨-366, ⟨1, 3, 0, 2, 1⟩⟩,
      ⟨-231, ⟨1, 2, 2, 1, 1⟩⟩,
      ⟨212, ⟨1, 2, 1, 3, 0⟩⟩,
      ⟨-375, ⟨1, 2, 0, 0, 3⟩⟩,
      ⟨112, ⟨1, 1, 4, 0, 1⟩⟩,
      ⟨-89, ⟨1, 1, 3, 2, 0⟩⟩,
      ⟨-3075, ⟨1, 1, 1, 1, 2⟩⟩,
      ⟨1640, ⟨1, 1, 0, 3, 1⟩⟩,
      ⟨6, ⟨1, 0, 5, 1, 0⟩⟩,
      ⟨-850, ⟨1, 0, 3, 0, 2⟩⟩,
      ⟨1220, ⟨1, 0, 2, 2, 1⟩⟩,
      ⟨-384, ⟨1, 0, 1, 4, 0⟩⟩,
      ⟨2500, ⟨1, 0, 0, 1, 3⟩⟩,
      ⟨-108, ⟨0, 5, 0, 0, 2⟩⟩,
      ⟨117, ⟨0, 4, 1, 1, 1⟩⟩,
      ⟨32, ⟨0, 4, 0, 3, 0⟩⟩,
      ⟨-31, ⟨0, 3, 3, 0, 1⟩⟩,
      ⟨-51, ⟨0, 3, 2, 2, 0⟩⟩,
      ⟨525, ⟨0, 3, 0, 1, 2⟩⟩,
      ⟨19, ⟨0, 2, 4, 1, 0⟩⟩,
      ⟨-325, ⟨0, 2, 2, 0, 2⟩⟩,
      ⟨260, ⟨0, 2, 1, 2, 1⟩⟩,
      ⟨-256, ⟨0, 2, 0, 4, 0⟩⟩,
      ⟨-2, ⟨0, 1, 6, 0, 0⟩⟩,
      ⟨105, ⟨0, 1, 3, 1, 1⟩⟩,
      ⟨76, ⟨0, 1, 2, 3, 0⟩⟩,
      ⟨625, ⟨0, 1, 1, 0, 3⟩⟩,
      ⟨-500, ⟨0, 1, 0, 2, 2⟩⟩,
      ⟨-58, ⟨0, 0, 5, 0, 1⟩⟩,
      ⟨3, ⟨0, 0, 4, 2, 0⟩⟩,
      ⟨2750, ⟨0, 0, 2, 1, 2⟩⟩,
      ⟨-2400, ⟨0, 0, 1, 3, 1⟩⟩,
      ⟨512, ⟨0, 0, 0, 5, 0⟩⟩,
      ⟨-3125, ⟨0, 0, 0, 0, 4⟩⟩
    ],
    [
      ⟨16, ⟨6, 0, 0, 0, 2⟩⟩,
      ⟨-8, ⟨5, 1, 0, 1, 1⟩⟩,
      ⟨-8, ⟨5, 0, 2, 0, 1⟩⟩,
      ⟨2, ⟨5, 0, 1, 2, 0⟩⟩,
      ⟨2, ⟨4, 2, 1, 0, 1⟩⟩,
      ⟨1, ⟨4, 2, 0, 2, 0⟩⟩,
      ⟨-120, ⟨4, 1, 0, 0, 2⟩⟩,
      ⟨68, ⟨4, 0, 1, 1, 1⟩⟩,
      ⟨-8, ⟨4, 0, 0, 3, 0⟩⟩,
      ⟨46, ⟨3, 2, 0, 1, 1⟩⟩,
      ⟨28, ⟨3, 1, 2, 0, 1⟩⟩,
      ⟨-19, ⟨3, 1, 1, 2, 0⟩⟩,
      ⟨250, ⟨3, 0, 1, 0, 2⟩⟩,
      ⟨-144, ⟨3, 0, 0, 2, 1⟩⟩,
      ⟨-9, ⟨2, 3, 1, 0, 1⟩⟩,
      ⟨-6, ⟨2, 3, 0, 2, 0⟩⟩,
      ⟨3, ⟨2, 2, 2, 1, 0⟩⟩,
      ⟨225, ⟨2, 2, 0, 0, 2⟩⟩,
      ⟨-354, ⟨2, 1, 1, 1, 1⟩⟩,
      ⟨76, ⟨2, 1, 0, 3, 0⟩⟩,
      ⟨-70, ⟨2, 0, 3, 0, 1⟩⟩,
      ⟨41, ⟨2, 0, 2, 2, 0⟩⟩,
      ⟨-200, ⟨2, 0, 0, 1, 2⟩⟩,
      ⟨-54, ⟨1, 3, 0, 1, 1⟩⟩,
      ⟨45, ⟨1, 2, 2, 0, 1⟩⟩,
      ⟨30, ⟨1, 2, 1, 2, 0⟩⟩,
      ⟨-19, ⟨1, 1, 3, 1, 0⟩⟩,
      ⟨-875, ⟨1, 1, 1, 0, 2⟩⟩,
      ⟨640, ⟨1, 1, 0, 2, 1⟩⟩,
      ⟨2, ⟨1, 0, 5, 0, 0⟩⟩,
      ⟨630, ⟨1, 0, 2, 1, 1⟩⟩,
      ⟨-264, ⟨1, 0, 1, 3, 0⟩⟩,
      ⟨9, ⟨0, 4, 0, 2, 0⟩⟩,
      ⟨-6, ⟨0, 3, 2, 1, 0⟩⟩,
      ⟨1, ⟨0, 2, 4, 0, 0⟩⟩,
      ⟨90, ⟨0, 2, 1, 1, 1⟩⟩,
      ⟨-136, ⟨0, 2, 0, 3, 0⟩⟩,
      ⟨-50, ⟨0, 1, 3, 0, 1⟩⟩,
      ⟨76, ⟨0, 1, 2, 2, 0⟩⟩,
      ⟨500, ⟨0, 1, 0, 1, 2⟩⟩,
      ⟨-8, ⟨0, 0, 4, 1, 0⟩⟩,
      ⟨625, ⟨0, 0, 2, 0, 2⟩⟩,
      ⟨-1400, ⟨0, 0, 1, 2, 1⟩⟩,
      ⟨400, ⟨0, 0, 0, 4, 0⟩⟩
    ],
    [
      ⟨16, ⟨4, 0, 1, 0, 1⟩⟩,
      ⟨-2, ⟨4, 0, 0, 2, 0⟩⟩,
      ⟨-2, ⟨3, 2, 0, 0, 1⟩⟩,
      ⟨-2, ⟨3, 1, 1, 1, 0⟩⟩,
      ⟨-44, ⟨3, 0, 0, 1, 1⟩⟩,
      ⟨-66, ⟨2, 1, 1, 0, 1⟩⟩,
      ⟨21, ⟨2, 1, 0, 2, 0⟩⟩,
      ⟨6, ⟨2, 0, 2, 1, 0⟩⟩,
      ⟨-50, ⟨2, 0, 0, 0, 2⟩⟩,
      ⟨9, ⟨1, 3, 0, 0, 1⟩⟩,
      ⟨5, ⟨1, 2, 1, 1, 0⟩⟩,
      ⟨-2, ⟨1, 1, 3, 0, 0⟩⟩,
      ⟨190, ⟨1, 1, 0, 1, 1⟩⟩,
      ⟨120, ⟨1, 0, 2, 0, 1⟩⟩,
      ⟨-80, ⟨1, 0, 1, 2, 0⟩⟩,
      ⟨-15, ⟨0, 2, 1, 0, 1⟩⟩,
      ⟨-40, ⟨0, 2, 0, 2, 0⟩⟩,
      ⟨21, ⟨0, 1, 2, 1, 0⟩⟩,
      ⟨125, ⟨0, 1, 0, 0, 2⟩⟩,
      ⟨-2, ⟨0, 0, 4, 0, 0⟩⟩,
      ⟨-400, ⟨0, 0, 1, 1, 1⟩⟩,
      ⟨160, ⟨0, 0, 0, 3, 0⟩⟩
    ],
    [
      ⟨-8, ⟨3, 0, 0, 0, 1⟩⟩,
      ⟨2, ⟨2, 1, 0, 1, 0⟩⟩,
      ⟨1, ⟨2, 0, 2, 0, 0⟩⟩,
      ⟨30, ⟨1, 1, 0, 0, 1⟩⟩,
      ⟨-14, ⟨1, 0, 1, 1, 0⟩⟩,
      ⟨-6, ⟨0, 2, 0, 1, 0⟩⟩,
      ⟨2, ⟨0, 1, 2, 0, 0⟩⟩,
      ⟨-50, ⟨0, 0, 1, 0, 1⟩⟩,
      ⟨40, ⟨0, 0, 0, 2, 0⟩⟩
    ],
    [
      ⟨-2, ⟨1, 0, 1, 0, 0⟩⟩,
      ⟨8, ⟨0, 0, 0, 1, 0⟩⟩
    ],
    [
      ⟨1, ⟨0, 0, 0, 0, 0⟩⟩
    ]
  ]

/-- Directly evaluate the certified sparse table at the signed coefficients
of a monic integral quintic. -/
def explicitDummitCoefficients (f : MonicQuintic) : IntegerSextic :=
  fun n => SparsePolynomial.eval (dummitTable n)
    (QuinticDummitCoefficients.elementaryCoefficients f)

noncomputable def SparseTerm.toMvPolynomial (t : SparseTerm) :
    MvPolynomial (Fin 5) ℤ :=
  MvPolynomial.C t.coeff *
    MvPolynomial.X 0 ^ t.powers.p0 *
    MvPolynomial.X 1 ^ t.powers.p1 *
    MvPolynomial.X 2 ^ t.powers.p2 *
    MvPolynomial.X 3 ^ t.powers.p3 *
    MvPolynomial.X 4 ^ t.powers.p4

noncomputable def SparsePolynomial.toMvPolynomial :
    SparsePolynomial → MvPolynomial (Fin 5) ℤ
  | [] => 0
  | t :: q => t.toMvPolynomial + SparsePolynomial.toMvPolynomial q

theorem eval_eq_eval₂_toMvPolynomial {R : Type*} [CommRing R]
    (q : SparsePolynomial) (x : Fin 5 → R) :
    SparsePolynomial.eval q x =
      MvPolynomial.eval₂Hom (Int.castRingHom R) x
        (SparsePolynomial.toMvPolynomial q) := by
  induction q with
  | nil => simp [SparsePolynomial.eval, SparsePolynomial.toMvPolynomial]
  | cons t q ih =>
      rw [SparsePolynomial.eval, SparsePolynomial.toMvPolynomial, map_add, ← ih]
      congr 1
      simp only [SparseTerm.eval, SparseTerm.toMvPolynomial, map_mul, map_pow,
        MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]
      rfl

/-! ## A proved executable sparse normalization procedure

The five stable radix passes make the normal form deterministic. Soundness
uses only that each pass preserves evaluation and that adjacent like powers
may be combined.
-/

def Powers.zero : Powers := ⟨0, 0, 0, 0, 0⟩

def Powers.add (a b : Powers) : Powers :=
  ⟨a.p0 + b.p0, a.p1 + b.p1, a.p2 + b.p2, a.p3 + b.p3, a.p4 + b.p4⟩

def SparseTerm.mul (a b : SparseTerm) : SparseTerm :=
  ⟨a.coeff * b.coeff, a.powers.add b.powers⟩

def SparseTerm.neg (a : SparseTerm) : SparseTerm :=
  ⟨-a.coeff, a.powers⟩

@[simp] theorem SparseTerm.eval_mul {R : Type*} [CommRing R]
    (a b : SparseTerm) (x : Fin 5 → R) :
    (a.mul b).eval x = a.eval x * b.eval x := by
  simp [SparseTerm.mul, SparseTerm.eval, Powers.add, pow_add]
  ring

@[simp] theorem SparseTerm.eval_neg {R : Type*} [CommRing R]
    (a : SparseTerm) (x : Fin 5 → R) :
    a.neg.eval x = -a.eval x := by
  simp [SparseTerm.neg, SparseTerm.eval]

theorem SparsePolynomial.eval_append {R : Type*} [CommRing R]
    (p q : SparsePolynomial) (x : Fin 5 → R) :
    SparsePolynomial.eval (p ++ q) x =
      SparsePolynomial.eval p x + SparsePolynomial.eval q x := by
  induction p with
  | nil => simp [SparsePolynomial.eval]
  | cons t p ih => simp [SparsePolynomial.eval, ih, add_assoc]

def SparsePolynomial.finish (t : SparseTerm) : SparsePolynomial :=
  if t.coeff = 0 then [] else [t]

def SparsePolynomial.combineAux (t : SparseTerm) :
    SparsePolynomial → SparsePolynomial
  | [] => finish t
  | u :: q =>
      if t.powers = u.powers then
        combineAux ⟨t.coeff + u.coeff, t.powers⟩ q
      else
        finish t ++ combineAux u q

def SparsePolynomial.combine : SparsePolynomial → SparsePolynomial
  | [] => []
  | t :: q => combineAux t q

theorem SparsePolynomial.eval_finish {R : Type*} [CommRing R]
    (t : SparseTerm) (x : Fin 5 → R) :
    SparsePolynomial.eval (finish t) x = t.eval x := by
  simp only [finish]
  split
  · rename_i h
    simp [SparsePolynomial.eval, SparseTerm.eval, h]
  · simp [SparsePolynomial.eval]

theorem SparseTerm.eval_add_of_powers_eq {R : Type*} [CommRing R]
    (t u : SparseTerm) (x : Fin 5 → R) (h : t.powers = u.powers) :
    SparseTerm.eval ⟨t.coeff + u.coeff, t.powers⟩ x =
      t.eval x + u.eval x := by
  rcases t with ⟨tc, tp⟩
  rcases u with ⟨uc, up⟩
  simp only at h
  subst up
  simp [SparseTerm.eval]
  ring

theorem SparsePolynomial.eval_combineAux {R : Type*} [CommRing R]
    (t : SparseTerm) (q : SparsePolynomial) (x : Fin 5 → R) :
    SparsePolynomial.eval (combineAux t q) x =
      t.eval x + SparsePolynomial.eval q x := by
  induction q generalizing t with
  | nil => simp [combineAux, eval_finish, SparsePolynomial.eval]
  | cons u q ih =>
      simp only [combineAux]
      split
      · rename_i h
        rw [ih, SparseTerm.eval_add_of_powers_eq t u x h]
        simp [SparsePolynomial.eval, add_assoc]
      · rw [SparsePolynomial.eval_append, eval_finish, ih]
        simp [SparsePolynomial.eval]

theorem SparsePolynomial.eval_combine {R : Type*} [CommRing R]
    (q : SparsePolynomial) (x : Fin 5 → R) :
    SparsePolynomial.eval (combine q) x = SparsePolynomial.eval q x := by
  cases q with
  | nil => rfl
  | cons t q =>
      simp [combine, eval_combineAux, SparsePolynomial.eval]

def SparsePolynomial.addToBucket :
    ℕ → SparseTerm → List SparsePolynomial → List SparsePolynomial
  | 0, t, [] => [[t]]
  | 0, t, b :: bs => (t :: b) :: bs
  | k + 1, t, [] => [] :: addToBucket k t []
  | k + 1, t, b :: bs => b :: addToBucket k t bs

def SparsePolynomial.bucketize (key : SparseTerm → ℕ) :
    SparsePolynomial → List SparsePolynomial
  | [] => []
  | t :: q => addToBucket (key t) t (bucketize key q)

def SparsePolynomial.flattenBuckets : List SparsePolynomial → SparsePolynomial
  | [] => []
  | b :: bs => b ++ flattenBuckets bs

theorem SparsePolynomial.eval_flattenBuckets_addToBucket
    {R : Type*} [CommRing R] (k : ℕ) (t : SparseTerm)
    (bs : List SparsePolynomial) (x : Fin 5 → R) :
    SparsePolynomial.eval (flattenBuckets (addToBucket k t bs)) x =
      t.eval x + SparsePolynomial.eval (flattenBuckets bs) x := by
  induction k generalizing bs with
  | zero =>
      cases bs <;>
        simp [addToBucket, flattenBuckets, SparsePolynomial.eval, eval_append]
  | succ k ih =>
      cases bs with
      | nil => simp [addToBucket, flattenBuckets, ih, SparsePolynomial.eval]
      | cons b bs =>
          simp [addToBucket, flattenBuckets, eval_append, ih]
          ring

def SparsePolynomial.radixPass (key : SparseTerm → ℕ)
    (q : SparsePolynomial) : SparsePolynomial :=
  flattenBuckets (bucketize key q)

theorem SparsePolynomial.eval_radixPass {R : Type*} [CommRing R]
    (key : SparseTerm → ℕ) (q : SparsePolynomial) (x : Fin 5 → R) :
    SparsePolynomial.eval (radixPass key q) x = SparsePolynomial.eval q x := by
  induction q with
  | nil => rfl
  | cons t q ih =>
      change SparsePolynomial.eval (flattenBuckets (bucketize key q)) x =
        SparsePolynomial.eval q x at ih
      rw [radixPass, bucketize, eval_flattenBuckets_addToBucket, ih]
      rfl

/-- Stable least-significant-coordinate-first radix sort of the five powers. -/
def SparsePolynomial.sort (q : SparsePolynomial) : SparsePolynomial :=
  radixPass (fun t ↦ t.powers.p0)
    (radixPass (fun t ↦ t.powers.p1)
      (radixPass (fun t ↦ t.powers.p2)
        (radixPass (fun t ↦ t.powers.p3)
          (radixPass (fun t ↦ t.powers.p4) q))))

theorem SparsePolynomial.eval_sort {R : Type*} [CommRing R]
    (q : SparsePolynomial) (x : Fin 5 → R) :
    SparsePolynomial.eval (sort q) x = SparsePolynomial.eval q x := by
  simp [sort, eval_radixPass]

def SparsePolynomial.normalize (q : SparsePolynomial) : SparsePolynomial :=
  combine (sort q)

theorem SparsePolynomial.eval_normalize {R : Type*} [CommRing R]
    (q : SparsePolynomial) (x : Fin 5 → R) :
    SparsePolynomial.eval (normalize q) x = SparsePolynomial.eval q x := by
  rw [normalize, eval_combine]
  exact eval_sort q x

def SparsePolynomial.rawNeg (p : SparsePolynomial) : SparsePolynomial :=
  p.map SparseTerm.neg

def SparsePolynomial.rawMul :
    SparsePolynomial → SparsePolynomial → SparsePolynomial
  | [], _ => []
  | t :: p, q => q.map (SparseTerm.mul t) ++ rawMul p q

theorem SparsePolynomial.eval_rawNeg {R : Type*} [CommRing R]
    (p : SparsePolynomial) (x : Fin 5 → R) :
    SparsePolynomial.eval (rawNeg p) x = -SparsePolynomial.eval p x := by
  induction p with
  | nil => simp [rawNeg, SparsePolynomial.eval]
  | cons t p ih =>
      simp only [rawNeg, List.map_cons, SparsePolynomial.eval,
        SparseTerm.eval_neg]
      change -t.eval x + SparsePolynomial.eval (rawNeg p) x =
        -(t.eval x + SparsePolynomial.eval p x)
      rw [ih]
      ring

theorem SparsePolynomial.eval_map_mul {R : Type*} [CommRing R]
    (t : SparseTerm) (q : SparsePolynomial) (x : Fin 5 → R) :
    SparsePolynomial.eval (q.map (SparseTerm.mul t)) x =
      t.eval x * SparsePolynomial.eval q x := by
  induction q with
  | nil => simp [SparsePolynomial.eval]
  | cons u q ih =>
      simp [SparsePolynomial.eval, ih, mul_add]

theorem SparsePolynomial.eval_rawMul {R : Type*} [CommRing R]
    (p q : SparsePolynomial) (x : Fin 5 → R) :
    SparsePolynomial.eval (rawMul p q) x =
      SparsePolynomial.eval p x * SparsePolynomial.eval q x := by
  induction p with
  | nil => simp [rawMul, SparsePolynomial.eval]
  | cons t p ih =>
      simp [rawMul, eval_append, eval_map_mul, ih,
        SparsePolynomial.eval, add_mul]

def SparsePolynomial.add (p q : SparsePolynomial) : SparsePolynomial :=
  normalize (p ++ q)

def SparsePolynomial.neg (p : SparsePolynomial) : SparsePolynomial :=
  normalize (rawNeg p)

def SparsePolynomial.mul (p q : SparsePolynomial) : SparsePolynomial :=
  normalize (rawMul p q)

def SparsePolynomial.const (z : ℤ) : SparsePolynomial :=
  normalize [⟨z, Powers.zero⟩]

def SparsePolynomial.pow (p : SparsePolynomial) : ℕ → SparsePolynomial
  | 0 => const 1
  | n + 1 => mul (pow p n) p

@[simp] theorem SparsePolynomial.eval_add {R : Type*} [CommRing R]
    (p q : SparsePolynomial) (x : Fin 5 → R) :
    SparsePolynomial.eval (add p q) x =
      SparsePolynomial.eval p x + SparsePolynomial.eval q x := by
  simp [add, eval_normalize, eval_append]

@[simp] theorem SparsePolynomial.eval_neg {R : Type*} [CommRing R]
    (p : SparsePolynomial) (x : Fin 5 → R) :
    SparsePolynomial.eval (neg p) x = -SparsePolynomial.eval p x := by
  simp [neg, eval_normalize, eval_rawNeg]

@[simp] theorem SparsePolynomial.eval_mul {R : Type*} [CommRing R]
    (p q : SparsePolynomial) (x : Fin 5 → R) :
    SparsePolynomial.eval (mul p q) x =
      SparsePolynomial.eval p x * SparsePolynomial.eval q x := by
  simp [mul, eval_normalize, eval_rawMul]

@[simp] theorem SparsePolynomial.eval_const {R : Type*} [CommRing R]
    (z : ℤ) (x : Fin 5 → R) :
    SparsePolynomial.eval (const z) x = z := by
  simp [const, eval_normalize, SparsePolynomial.eval, SparseTerm.eval,
    Powers.zero]

@[simp] theorem SparsePolynomial.eval_pow {R : Type*} [CommRing R]
    (p : SparsePolynomial) (n : ℕ) (x : Fin 5 → R) :
    SparsePolynomial.eval (pow p n) x = SparsePolynomial.eval p x ^ n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => simp [pow, ih, pow_succ]

def elementaryTuple {R : Type*} [CommRing R] (x : Fin 5 → R) : Fin 5 → R :=
  ![x 0 + x 1 + x 2 + x 3 + x 4,
    x 0 * x 1 + x 0 * x 2 + x 0 * x 3 + x 0 * x 4 +
      x 1 * x 2 + x 1 * x 3 + x 1 * x 4 + x 2 * x 3 + x 2 * x 4 + x 3 * x 4,
    x 0 * x 1 * x 2 + x 0 * x 1 * x 3 + x 0 * x 1 * x 4 +
      x 0 * x 2 * x 3 + x 0 * x 2 * x 4 + x 0 * x 3 * x 4 +
      x 1 * x 2 * x 3 + x 1 * x 2 * x 4 + x 1 * x 3 * x 4 + x 2 * x 3 * x 4,
    x 0 * x 1 * x 2 * x 3 + x 0 * x 1 * x 2 * x 4 +
      x 0 * x 1 * x 3 * x 4 + x 0 * x 2 * x 3 * x 4 + x 1 * x 2 * x 3 * x 4,
    x 0 * x 1 * x 2 * x 3 * x 4]

def thetaRoot {R : Type*} [CommRing R] (x : Fin 5 → R) (i : Fin 6) : R :=
  FrobeniusDummitResolvent.thetaFormula
    (fun j => x (FrobeniusDummitResolvent.representative i j))

/-! ## Sparse substitution and the certificate source expressions -/

def SparsePolynomial.sum : List SparsePolynomial → SparsePolynomial
  | [] => []
  | p :: ps => add p (sum ps)

@[simp] theorem SparsePolynomial.eval_sum {R : Type*} [CommRing R]
    (ps : List SparsePolynomial) (x : Fin 5 → R) :
    SparsePolynomial.eval (sum ps) x =
      (ps.map (fun p ↦ SparsePolynomial.eval p x)).sum := by
  induction ps with
  | nil => simp [sum, SparsePolynomial.eval]
  | cons p ps ih => simp [sum, ih]

def Powers.basis : Fin 5 → Powers :=
  ![⟨1, 0, 0, 0, 0⟩, ⟨0, 1, 0, 0, 0⟩, ⟨0, 0, 1, 0, 0⟩,
    ⟨0, 0, 0, 1, 0⟩, ⟨0, 0, 0, 0, 1⟩]

def SparsePolynomial.varPoly (i : Fin 5) : SparsePolynomial :=
  [⟨1, Powers.basis i⟩]

@[simp] theorem SparsePolynomial.eval_varPoly {R : Type*} [CommRing R]
    (i : Fin 5) (x : Fin 5 → R) :
    SparsePolynomial.eval (varPoly i) x = x i := by
  fin_cases i <;>
    simp [varPoly, Powers.basis, SparsePolynomial.eval, SparseTerm.eval]

def elementaryPolynomials : Fin 5 → SparsePolynomial :=
  let x := SparsePolynomial.varPoly
  ![
    SparsePolynomial.sum [x 0, x 1, x 2, x 3, x 4],
    SparsePolynomial.sum
      [x 0 |>.mul (x 1), x 0 |>.mul (x 2), x 0 |>.mul (x 3),
       x 0 |>.mul (x 4), x 1 |>.mul (x 2), x 1 |>.mul (x 3),
       x 1 |>.mul (x 4), x 2 |>.mul (x 3), x 2 |>.mul (x 4),
       x 3 |>.mul (x 4)],
    SparsePolynomial.sum
      [(x 0 |>.mul (x 1)).mul (x 2), (x 0 |>.mul (x 1)).mul (x 3),
       (x 0 |>.mul (x 1)).mul (x 4), (x 0 |>.mul (x 2)).mul (x 3),
       (x 0 |>.mul (x 2)).mul (x 4), (x 0 |>.mul (x 3)).mul (x 4),
       (x 1 |>.mul (x 2)).mul (x 3), (x 1 |>.mul (x 2)).mul (x 4),
       (x 1 |>.mul (x 3)).mul (x 4), (x 2 |>.mul (x 3)).mul (x 4)],
    SparsePolynomial.sum
      [((x 0 |>.mul (x 1)).mul (x 2)).mul (x 3),
       ((x 0 |>.mul (x 1)).mul (x 2)).mul (x 4),
       ((x 0 |>.mul (x 1)).mul (x 3)).mul (x 4),
       ((x 0 |>.mul (x 2)).mul (x 3)).mul (x 4),
       ((x 1 |>.mul (x 2)).mul (x 3)).mul (x 4)],
    (((x 0 |>.mul (x 1)).mul (x 2)).mul (x 3)).mul (x 4)
  ]

theorem eval_elementaryPolynomials {R : Type*} [CommRing R]
    (i : Fin 5) (x : Fin 5 → R) :
    SparsePolynomial.eval (elementaryPolynomials i) x = elementaryTuple x i := by
  fin_cases i <;>
    simp [elementaryPolynomials, elementaryTuple] <;> ring

def SparseTerm.substitute (t : SparseTerm)
    (p : Fin 5 → SparsePolynomial) : SparsePolynomial :=
  SparsePolynomial.mul (SparsePolynomial.const t.coeff)
    (SparsePolynomial.mul (SparsePolynomial.pow (p 0) t.powers.p0)
      (SparsePolynomial.mul (SparsePolynomial.pow (p 1) t.powers.p1)
        (SparsePolynomial.mul (SparsePolynomial.pow (p 2) t.powers.p2)
          (SparsePolynomial.mul (SparsePolynomial.pow (p 3) t.powers.p3)
            (SparsePolynomial.pow (p 4) t.powers.p4)))))

def SparsePolynomial.substitute :
    SparsePolynomial → (Fin 5 → SparsePolynomial) → SparsePolynomial
  | [], _ => []
  | t :: q, p => add (t.substitute p) (substitute q p)

@[simp] theorem SparseTerm.eval_substitute {R : Type*} [CommRing R]
    (t : SparseTerm) (p : Fin 5 → SparsePolynomial) (x : Fin 5 → R) :
    SparsePolynomial.eval (t.substitute p) x =
      t.eval (fun i ↦ SparsePolynomial.eval (p i) x) := by
  simp [SparseTerm.substitute, SparseTerm.eval]
  ring

theorem SparsePolynomial.eval_substitute {R : Type*} [CommRing R]
    (q : SparsePolynomial) (p : Fin 5 → SparsePolynomial) (x : Fin 5 → R) :
    SparsePolynomial.eval (substitute q p) x =
      SparsePolynomial.eval q (fun i ↦ SparsePolynomial.eval (p i) x) := by
  induction q with
  | nil => simp [substitute, SparsePolynomial.eval]
  | cons t q ih => simp [substitute, SparsePolynomial.eval, ih]

def sparseThetaFormula (r : Fin 5 → SparsePolynomial) : SparsePolynomial :=
  let term (i j k : Fin 5) :=
    (SparsePolynomial.pow (r i) 2 |>.mul (r j)).mul (r k)
  SparsePolynomial.sum
    [term 0 1 4, term 0 2 3, term 1 0 2, term 1 3 4,
     term 2 0 4, term 2 1 3, term 3 0 1, term 3 2 4,
     term 4 0 3, term 4 1 2]

theorem eval_sparseThetaFormula {R : Type*} [CommRing R]
    (r : Fin 5 → SparsePolynomial) (x : Fin 5 → R) :
    SparsePolynomial.eval (sparseThetaFormula r) x =
      FrobeniusDummitResolvent.thetaFormula
        (fun i ↦ SparsePolynomial.eval (r i) x) := by
  simp [sparseThetaFormula, FrobeniusDummitResolvent.thetaFormula]
  ring

def thetaPolynomial (i : Fin 6) : SparsePolynomial :=
  sparseThetaFormula (fun j ↦
    SparsePolynomial.varPoly (FrobeniusDummitResolvent.representative i j))

@[simp] theorem eval_thetaPolynomial {R : Type*} [CommRing R]
    (i : Fin 6) (x : Fin 5 → R) :
    SparsePolynomial.eval (thetaPolynomial i) x = thetaRoot x i := by
  rw [thetaPolynomial, eval_sparseThetaFormula]
  simp [thetaRoot]

def thetaPolynomials : List SparsePolynomial :=
  [thetaPolynomial 0, thetaPolynomial 1, thetaPolynomial 2,
   thetaPolynomial 3, thetaPolynomial 4, thetaPolynomial 5]

def thetaRoots {R : Type*} [CommRing R] (x : Fin 5 → R) : List R :=
  [thetaRoot x 0, thetaRoot x 1, thetaRoot x 2,
   thetaRoot x 3, thetaRoot x 4, thetaRoot x 5]

def scalarEsymm {R : Type*} [CommRing R] : List R → ℕ → R
  | _, 0 => 1
  | [], _ + 1 => 0
  | a :: s, k + 1 => scalarEsymm s (k + 1) + a * scalarEsymm s k

def SparsePolynomial.esymm : List SparsePolynomial → ℕ → SparsePolynomial
  | _, 0 => const 1
  | [], _ + 1 => []
  | p :: ps, k + 1 => add (esymm ps (k + 1)) (mul p (esymm ps k))

theorem SparsePolynomial.eval_esymm {R : Type*} [CommRing R]
    (ps : List SparsePolynomial) (k : ℕ) (x : Fin 5 → R) :
    SparsePolynomial.eval (esymm ps k) x =
      scalarEsymm (ps.map (fun p ↦ SparsePolynomial.eval p x)) k := by
  induction ps generalizing k with
  | nil => cases k <;> simp [esymm, scalarEsymm, SparsePolynomial.eval]
  | cons p ps ih => cases k <;> simp [esymm, scalarEsymm, ih]

def sparseRootCoefficient (n : Fin 7) : SparsePolynomial :=
  let k := 6 - (n : ℕ)
  SparsePolynomial.mul (SparsePolynomial.const ((-1 : ℤ) ^ k))
    (SparsePolynomial.esymm thetaPolynomials k)

def listRootCoefficient {R : Type*} [CommRing R]
    (x : Fin 5 → R) (n : Fin 7) : R :=
  let k := 6 - (n : ℕ)
  (-1 : R) ^ k * scalarEsymm (thetaRoots x) k

@[simp] theorem eval_sparseRootCoefficient {R : Type*} [CommRing R]
    (n : Fin 7) (x : Fin 5 → R) :
    SparsePolynomial.eval (sparseRootCoefficient n) x =
      listRootCoefficient x n := by
  simp [sparseRootCoefficient, listRootCoefficient,
    SparsePolynomial.eval_esymm, thetaPolynomials, thetaRoots]

def tableInRoots (n : Fin 7) : SparsePolynomial :=
  SparsePolynomial.substitute (dummitTable n) elementaryPolynomials

theorem eval_tableInRoots {R : Type*} [CommRing R]
    (n : Fin 7) (x : Fin 5 → R) :
    SparsePolynomial.eval (tableInRoots n) x =
      SparsePolynomial.eval (dummitTable n) (elementaryTuple x) := by
  rw [tableInRoots, SparsePolynomial.eval_substitute]
  apply congrArg (SparsePolynomial.eval (dummitTable n))
  funext i
  exact eval_elementaryPolynomials i x

theorem Multiset.esymm_cons_succ {R : Type*} [CommRing R]
    (a : R) (s : Multiset R) (k : ℕ) :
    (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := by
  simp [Multiset.esymm, Multiset.powersetCard_cons,
    Multiset.sum_map_mul_left]

theorem scalarEsymm_eq_multiset_esymm {R : Type*} [CommRing R]
    (s : List R) (k : ℕ) :
    scalarEsymm s k = (s : Multiset R).esymm k := by
  induction s generalizing k with
  | nil => cases k <;> simp [scalarEsymm, Multiset.esymm]
  | cons a s ih =>
      cases k with
      | zero => simp [scalarEsymm, Multiset.esymm]
      | succ k =>
          change scalarEsymm s (k + 1) + a * scalarEsymm s k =
            (a ::ₘ (s : Multiset R)).esymm (k + 1)
          rw [Multiset.esymm_cons_succ, ih, ih]

theorem thetaRoots_eq_ofFn {R : Type*} [CommRing R] (x : Fin 5 → R) :
    thetaRoots x = List.ofFn (thetaRoot x) := by
  simp [thetaRoots, List.ofFn_succ]

noncomputable def vietaRootCoefficient {R : Type*} [CommRing R]
    (x : Fin 5 → R) (n : Fin 7) : R :=
  (-1 : R) ^ (6 - (n : ℕ)) *
    (Finset.univ.val.map (thetaRoot x)).esymm (6 - (n : ℕ))

theorem listRootCoefficient_eq_vietaRootCoefficient
    {R : Type*} [CommRing R] (x : Fin 5 → R) (n : Fin 7) :
    listRootCoefficient x n = vietaRootCoefficient x n := by
  rw [listRootCoefficient, vietaRootCoefficient,
    scalarEsymm_eq_multiset_esymm, thetaRoots_eq_ofFn,
    ← Fin.univ_val_map]

theorem vietaRootCoefficient_eq_coeff_product
    {R : Type*} [CommRing R] (x : Fin 5 → R) (n : Fin 7) :
    vietaRootCoefficient x n =
      (∏ i : Fin 6,
        (Polynomial.X - Polynomial.C (thetaRoot x i))).coeff n := by
  have h := Multiset.prod_X_sub_C_coeff
    (R := R) (Finset.univ.val.map (thetaRoot x))
    (k := (n : ℕ)) (by
      simp only [Multiset.card_map, ← Finset.card_def,
        Finset.card_univ, Fintype.card_fin]
      omega)
  simpa [vietaRootCoefficient, Finset.prod,
    Multiset.map_map, Function.comp_def] using h.symm

theorem listRootCoefficient_eq_scalarResolvent_coeff
    {R : Type*} [CommRing R] (x : Fin 5 → R) (n : Fin 7) :
    listRootCoefficient x n =
      (FrobeniusDummitResolvent.scalarResolvent x).coeff n := by
  rw [listRootCoefficient_eq_vietaRootCoefficient,
    vietaRootCoefficient_eq_coeff_product,
    FrobeniusDummitResolvent.scalarResolvent_eq_prod]
  simp [thetaRoot, FrobeniusDummitResolvent.thetaValue_eq_thetaFormula]

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem normalized_table_certificate_zero :
    SparsePolynomial.normalize (tableInRoots 0) =
      SparsePolynomial.normalize (sparseRootCoefficient 0) := by
  native_decide

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem normalized_table_certificate_one :
    SparsePolynomial.normalize (tableInRoots 1) =
      SparsePolynomial.normalize (sparseRootCoefficient 1) := by
  native_decide

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem normalized_table_certificate_two :
    SparsePolynomial.normalize (tableInRoots 2) =
      SparsePolynomial.normalize (sparseRootCoefficient 2) := by
  native_decide

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem normalized_table_certificate_three :
    SparsePolynomial.normalize (tableInRoots 3) =
      SparsePolynomial.normalize (sparseRootCoefficient 3) := by
  native_decide

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem normalized_table_certificate_four :
    SparsePolynomial.normalize (tableInRoots 4) =
      SparsePolynomial.normalize (sparseRootCoefficient 4) := by
  decide

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem normalized_table_certificate_five :
    SparsePolynomial.normalize (tableInRoots 5) =
      SparsePolynomial.normalize (sparseRootCoefficient 5) := by
  decide

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 100000 in
theorem normalized_table_certificate_six :
    SparsePolynomial.normalize (tableInRoots 6) =
      SparsePolynomial.normalize (sparseRootCoefficient 6) := by
  decide

theorem normalized_table_certificate (n : Fin 7) :
    SparsePolynomial.normalize (tableInRoots n) =
      SparsePolynomial.normalize (sparseRootCoefficient n) := by
  fin_cases n
  · exact normalized_table_certificate_zero
  · exact normalized_table_certificate_one
  · exact normalized_table_certificate_two
  · exact normalized_table_certificate_three
  · exact normalized_table_certificate_four
  · exact normalized_table_certificate_five
  · exact normalized_table_certificate_six

theorem SparsePolynomial.eval_eq_of_normalize_eq
    {R : Type*} [CommRing R] {p q : SparsePolynomial}
    (h : normalize p = normalize q) (x : Fin 5 → R) :
    SparsePolynomial.eval p x = SparsePolynomial.eval q x := by
  calc
    SparsePolynomial.eval p x = SparsePolynomial.eval (normalize p) x :=
      (eval_normalize p x).symm
    _ = SparsePolynomial.eval (normalize q) x := congrArg (fun s ↦ eval s x) h
    _ = SparsePolynomial.eval q x := eval_normalize q x

theorem dummitTable_eval_elementaryTuple
    {R : Type*} [CommRing R] (n : Fin 7) (x : Fin 5 → R) :
    SparsePolynomial.eval (dummitTable n) (elementaryTuple x) =
      listRootCoefficient x n := by
  calc
    SparsePolynomial.eval (dummitTable n) (elementaryTuple x) =
        SparsePolynomial.eval (tableInRoots n) x :=
      (eval_tableInRoots n x).symm
    _ = SparsePolynomial.eval (sparseRootCoefficient n) x :=
      SparsePolynomial.eval_eq_of_normalize_eq
        (normalized_table_certificate n) x
    _ = listRootCoefficient x n := eval_sparseRootCoefficient n x

theorem table_six_identity {R : Type*} [CommRing R] (x : Fin 5 → R) :
    SparsePolynomial.eval (dummitTable 6) (elementaryTuple x) = 1 := by
  simp [dummitTable, SparsePolynomial.eval, SparseTerm.eval]

end LeanProofs.PolynomialFormulas.ComputableDummitCoefficients
