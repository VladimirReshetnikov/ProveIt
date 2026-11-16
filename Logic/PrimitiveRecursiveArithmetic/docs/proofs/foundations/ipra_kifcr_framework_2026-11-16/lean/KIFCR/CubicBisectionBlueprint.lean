import KIFCR.GraphBlueprint

/-!
# Closed benchmark blueprint: the inverse of y^3 + y on [0,1]

The intended theorem takes a rational-code input `x` with `0 <= x <= 1` and a
precision `k`, performs `k+3` exact rational bisection steps on `[0,1]`, and
returns a midpoint `m` with a certified bracket and residual/error bound.

This file records the exact definitions and proof decomposition.  It contains
no admitted theorem and is not claimed to compile in this artifact.
-/

namespace LeanProofs.KIFCR.Cubic

/-- Host-level polynomial used only for the semantic prototype. -/
def poly (x y : Int) : Int := y * y * y + y - x

/-- Host-level bisection state for executable prototyping.  The object version
uses signed rational codes and one packed primitive-recursive state. -/
structure State where
  loNum : Int
  hiNum : Int
  den : Nat
  deriving Repr, DecidableEq

/-!
Object definitions to generate:

* rational code `(p,m,d)` for `(p-m)/(d+1)`;
* `cubic x y = y*y*y + y - x` in integer-difference arithmetic;
* state `(lo,hi,step)` encoded by checked nested pairing;
* midpoint and exact sign comparison by cross multiplication;
* transition keeping `[mid,hi]` when `cubic x mid <= 0`, otherwise `[lo,mid]`;
* fuel `k+3` for represented inputs, or `k+1` for rational input with the
  chosen interval-length convention.

QF invariant:

1. `0 <= lo <= hi <= 1`;
2. `cubic x lo <= 0` and `0 <= cubic x hi`;
3. `hi - lo = 2^{-step}` as a cross-multiplied integer equality;
4. all rational denominators are positive;
5. the state is exactly the generated transition iterate.

Local algebra theorem:

`(y-z) * ((y^3+y-x) - (z^3+z-x))
 = (y-z)^2 * (y^2 + y*z + z^2 + 1)`.

Use `ipra_ring` for the identity and ordered-semiring lemmas for the lower
bound.  It gives uniqueness and the 1-Lipschitz parameter estimate without an
exact real-number choice.

Terminal theorem:

* the final midpoint lies in the certified bracket;
* bracket width is at most `2^-(k+3)`;
* for a represented input approximated at stage `k+3`, parameter transport is
  at most `2^-(k+3)`;
* total error is below `2^-k` after a deliberately slack budget.

The public endpoint should be a `ConditionalTheorem` only if rational-code or
input-name preconditions remain open; no real completeness axiom is needed.
-/

end LeanProofs.KIFCR.Cubic
