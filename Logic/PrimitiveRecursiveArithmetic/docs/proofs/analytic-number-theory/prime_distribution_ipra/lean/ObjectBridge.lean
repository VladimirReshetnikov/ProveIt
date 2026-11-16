import ConciseIPRA.NativeBiInterpretation

/-!
# Object-language integration interface

UNCOMPILED OUTLINE. This file is intended for the pinned ProveIt workspace,
with its `ConciseIPRA` library on Lean's import path.

The file contains only generic definitions and a conditional transport lemma.
It does not construct a Dirichlet, sieve, Chebotarev, SW, or BV proof.
In particular, `test` below must eventually be the actual compiled PR code
for the intended arithmetic matrix, accompanied by its correctness proof.
An arbitrary PR code is not a specification of the desired theorem.
-/

namespace PrimeDistributionObjectOutline

open LeanProofs.ConciseIPRA

/-- The open arithmetic formula saying that a Boolean PR program returns 1. -/
def boolFormula {k : Nat} (test : PR k) : Fm PTm k :=
  Fm.eq (PTm.app test (fun i => PTm.var i))
    (PTm.succ PTm.zero)

/-- The actual object-theory goal, with k universally free parameters. -/
def ArithmeticGoal {k : Nat} (test : PR k) : Prop :=
  Prf PRAAx [] (boolFormula test)

/-- Generic final transfer; its premise is the missing arithmetic derivation.
    This does not prove that premise. -/
theorem transferProvidedDerivation {k : Nat} (test : PR k)
    (h : ArithmeticGoal test) :
    NPrf [] (NFm.ofPRA (boolFormula test)) := by
  simpa [ArithmeticGoal] using
    (pra_iff_native (Γ := []) (φ := boolFormula test)).mp h

/-
Required fixed programs, to be constructed (not postulated):

1. Dirichlet matrix, arity 3: q, a, B.
   Invalid q or non-coprime input returns true.
   Valid input tests the factorial-scaled reciprocal sum at Y(q,B).

2. Finite Selberg matrix, arity 4: x, q, a, z.
   Clear positive rational denominators in the stated finite bound.

3. Asymptotic BT matrix, arity 5: k, x, q, a, precision.
   Use the exact root-search and logarithm-lower-approximation programs.

4. Sharp BT matrix for integer endpoints, arity 4: x, q, a, precision.
   Use the lower logarithm approximation and test phi(q)*pi(x;q,a)*L <= 2*x
   after clearing positive denominators. For rational endpoints, use arity 5
   with numerator and positive denominator in place of x.
   The proof modules are the finite-grid cosecant bound, weighted large
   sieve, Ramanujan sums, denominator certificate, and overlapping ranges.

5. Full SW and BV are quantified formulas, not just a single open matrix:
   retain the existential constants before all endpoint/precision variables.
   There is no derivation of those formulas in this package.

6. Chebotarev counting is defined only after certified number-field algorithms
   and their correctness derivations are supplied. The modulus reduction
   takes explicit analytic estimates as inputs; they remain unproved here.

Every mathematical theorem must end with ArithmeticGoal for its genuine
compiled program, or Prf PRAAx [] for its genuine quantified formula.
Semantic truth about Nat, Rat, Real, or Complex cannot fill this obligation.
-/

end PrimeDistributionObjectOutline
