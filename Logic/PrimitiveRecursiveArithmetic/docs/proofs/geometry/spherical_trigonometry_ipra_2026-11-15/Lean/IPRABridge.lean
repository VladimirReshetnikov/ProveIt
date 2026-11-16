import ConciseIPRA.PR
import ConciseIPRA.EqArith
import ConciseIPRA.NativeBiInterpretation

/-!
# Blueprint for lowering spherical trigonometry to ConciseIPRA

This file intentionally contains data structures and target types rather than
host-level axioms pretending that the implementation is complete.  A finished
development must construct a value of `InternalAtlasTarget` whose `derivation`
field is an actual `Prf PRAAx` term.

Repository target: ProveIt commit
`a3c053cc6243dca44824510fac104958d616a6b9`.
-/

namespace LeanProofs.ConciseIPRA.Spherical

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm

/-- Signed integer represented by positive and negative parts. -/
structure SIntCode where
  pos : Nat
  neg : Nat

/-- A dyadic `(pos-neg)/2^exp`, represented at the meta level. -/
structure DyadicCode where
  num : SIntCode
  exp : Nat

/-- A fixed primitive-recursive rapid-name program.

`approx` returns a natural code for a dyadic approximation.  Regularity is not
a Lean `Prop` field here: the completed object includes an object-language
formula and a `Prf PRAAx` derivation of it.
-/
structure RealNameCode where
  approx : PR 1
  magnitudeBound : Nat

structure V3NameCode where
  x : RealNameCode
  y : RealNameCode
  z : RealNameCode

/-- Finite positive-separation information used to compile a reciprocal. -/
structure ApartWitnessCode where
  samplePrecision : Nat
  lowerExponent : Nat
  positiveSign : Bool

/-- Fixed input programs and branch certificates for one proper triangle. -/
structure SphericalInputCode where
  u v w : V3NameCode
  sideSineA sideSineB sideSineC : ApartWitnessCode
  orientation : ApartWitnessCode

/-- Fixed coordinate programs for a tetrahedron. -/
structure TetrahedronInputCode where
  p1 p2 p3 p4 : V3NameCode
  faceNondegenerate : Fin 4 → ApartWitnessCode

/-- Explicit exponential truncation schedule reused from the trig packet. -/
def expTerms (B p : Nat) : Nat := 2 * B * B + 2 * B + p + 4

/-- A deliberately coarse bounded-search range for a dyadic square root. -/
def sqrtScanBound (integerBound precision : Nat) : Nat :=
  (integerBound + 2) * (2 ^ precision)

/-- Precision shift for a reciprocal from a lower bound `2^-k`.
The completed proof may replace this coarse value by a smaller certified one. -/
def reciprocalShift (k p : Nat) : Nat := p + 2*k + 8

/-- A closed internal theorem package.  Constructing this structure is the
acceptance criterion for the object-level formalization. -/
structure InternalAtlasTarget where
  hypotheses : Fm PTm 0
  conclusions : Fm PTm 0
  derivation : Prf PRAAx [] (hypotheses ⟶ conclusions)

/-- Separate target for the tetrahedral area-vector theorem. -/
structure InternalTetrahedronTarget where
  hypotheses : Fm PTm 0
  conclusions : Fm PTm 0
  derivation : Prf PRAAx [] (hypotheses ⟶ conclusions)

/-!
Implementation order

1. Define natural codecs for signed integers, positive-denominator rationals,
   dyadics, fixed tuples and finite sparse polynomials as concrete `PR` terms.
2. Prove their defining equations with `PRA.proj`, `PRA.comp`,
   `PRA.precZero`, and `PRA.precSucc`.
3. Implement rational comparison, bounded maximum/search, dot/cross/determinant,
   the dyadic square-root scan, finite exponential and arctangent sums.
4. Encode rapid-name regularity, equality, bounds and apartness as
   `Fm PTm n`; prove closure using `PRA.qfInd` with the precision free.
5. Implement and internally verify the polynomial certificate normalizer for
   the spherical core ideal and the tetrahedral face-closure identity.
6. Compile the fixed input programs to the output side/angle programs and prove
   every finite error estimate.
7. Build the closed formulas and finally construct `InternalAtlasTarget` and
   `InternalTetrahedronTarget` values.
8. Only then use `pra_iff_native` to transport the completed derivations.

No total universal evaluator for arbitrary PR syntax is assumed.  Each theorem
is a schema over the fixed `PR` programs stored in one `SphericalInputCode` or
`TetrahedronInputCode`.
-/

end LeanProofs.ConciseIPRA.Spherical
