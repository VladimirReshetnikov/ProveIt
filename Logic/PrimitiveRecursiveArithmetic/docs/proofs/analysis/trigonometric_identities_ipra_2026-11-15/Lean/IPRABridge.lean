import ConciseIPRA.PR
import ConciseIPRA.EqArith

/-!
# Blueprint for lowering constructive trigonometry to ConciseIPRA

This is a signature-level formalization plan, not a completed implementation.
It fixes the data representations and theorem interfaces needed for a direct
extension of `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean`.

The decisive design choice is that iPRA does not quantify over functions or
over an already existing real-number sort.  A "constructive real variable" is
therefore a fixed primitive-recursive interval-name term together with an iPRA
certificate of regularity.  Every theorem in the article denotes a uniform
proof-producing schema over such terms.  No universal primitive-recursive
evaluator is assumed.
-/

namespace LeanProofs.ConciseIPRA.Trig

open LeanProofs.ConciseIPRA

/-- Signed integers may be represented by a pair `(positive, negative)`. -/
structure SInt where
  pos : Nat
  neg : Nat

/-- The dyadic `(num.pos-num.neg)/2^exp`. -/
structure Dyadic where
  num : SInt
  exp : Nat

/-- Closed rational interval with a common dyadic denominator. -/
structure DInterval where
  lower : Dyadic
  upper : Dyadic

/-- A syntactic primitive-recursive interval name.

`lowerCode` and `upperCode` are unary primitive-recursive function symbols in
the sense of `ConciseIPRA.PR`.  The proof fields are not Lean propositions
about standard naturals in the final development: they are derivations
`Γ ⊢[PRAAx] A` of the corresponding arithmetized formulas.
-/
structure RealNameCode where
  lowerCode : PR 1
  upperCode : PR 1
  magnitudeBound : Nat

/-- A complex name is a pair of real names. -/
structure ComplexNameCode where
  re : RealNameCode
  im : RealNameCode

/-- Precision shift used by the exponential tail estimate.
For `B >= 1`, every tail beginning at this index is below `2^(-p-2)`.
-/
def expTerms (B p : Nat) : Nat := 2 * B * B + 2 * B + p + 4

/-- A witness that a real is apart from zero.  Semantically it supplies a
positive dyadic lower bound, and therefore enough information to compute a
reciprocal. -/
structure ApartWitness where
  precision : Nat
  lowerExponent : Nat

/-- Branch data for a square root or an inverse trigonometric function. -/
inductive SignRegion
  | nonnegative
  | nonpositive
  | principal

/-!
Planned arithmetized predicates (shown as declarations to make dependencies
explicit):

* `Regular a`: nested intervals, ordered endpoints, width at most `2^-p`;
* `EqReal a b`: the intervals meet to every requested precision;
* `LtReal a b k`: a precision-`k` strict separation witness;
* `Apart a k`: either `a > 2^-k` or `a < -2^-k`;
* `Bounds a B`: every interval lies in `[-B,B]`.

Each is a first-order formula over `PTm`; the defining operations below are
primitive-recursive term constructors.  Their closure proofs use
`PRA.qfInd` from `ConciseIPRA.PR`.
-/

axiom Regular : RealNameCode → Prop
axiom EqReal : RealNameCode → RealNameCode → Prop
axiom Apart : RealNameCode → ApartWitness → Prop
axiom Bounds : RealNameCode → Nat → Prop

axiom zero : RealNameCode
axiom one : RealNameCode
axiom neg : RealNameCode → RealNameCode
axiom add : RealNameCode → RealNameCode → RealNameCode
axiom mul : RealNameCode → RealNameCode → RealNameCode
axiom inv : (a : RealNameCode) → ApartWitness → RealNameCode
axiom sqrt : (a : RealNameCode) → SignRegion → RealNameCode

axiom cexp : ComplexNameCode → ComplexNameCode
axiom sin : RealNameCode → RealNameCode
axiom cos : RealNameCode → RealNameCode

/-- The primitive-recursive bounded-search name for the unique zero of cosine
in `(1,2)`. -/
axiom quarterTurn : RealNameCode
axiom pi : RealNameCode

/-- Analytic realization targets.  In the final development these are
arithmetized derivability statements rather than metatheoretic `Prop`s. -/
axiom cexp_add (x y : ComplexNameCode) :
  True  -- `EqComplex (cexp (x+y)) (cexp x * cexp y)`

axiom pythagorean (x : RealNameCode) :
  EqReal (add (mul (sin x) (sin x)) (mul (cos x) (cos x))) one

axiom quarterTurn_spec :
  EqReal (cos quarterTurn) zero

axiom quarterTurn_sine :
  EqReal (sin quarterTurn) one

/-!
Concrete completion order

1. Define signed integer and dyadic arithmetic as `PR` symbols and prove their
   equations with `PRA.proj`, `PRA.comp`, `PRA.precZero`, and `PRA.precSucc`.
2. Encode interval predicates as quantifier-free formulas and prove closure of
   regular names under `neg`, `add`, and bounded `mul` by `PRA.qfInd`.
3. Add interval inversion from `ApartWitness` and interval square-root
   bisection from explicit sign bounds.
4. Implement finite exponential sums and prove the factorial/geometric tail
   lemma using the explicit `expTerms` modulus.
5. Prove the finite Cauchy-product coefficient identity, then `cexp_add`.
6. Define `sin` and `cos`, derive addition and Pythagorean laws, and implement
   the bounded bisection name `quarterTurn`.
7. Import the algebraic certificate syntax and prove evaluator soundness by
   structural induction and quantifier-free induction on finite lists.
-/

end LeanProofs.ConciseIPRA.Trig
