/-!
# Lagrange inversion in iPRA: Lean formalization blueprint

This file is deliberately a blueprint, not a completed formalization.  It is
written against the APIs present in Mathlib v4.32.0 and the ProveIt
`ConciseIPRA` library at the repository snapshot recorded in SOURCES.md.
No theorem below is claimed to be kernel checked merely because its target is
shown here.

The recommended implementation has two layers:

1. an abstract `PowerSeries` proof over a commutative Q-algebra;
2. a finite `TruncSeries` implementation whose algorithms and correctness
   proofs are compiled into `ConciseIPRA.PR` and transported with
   `pra_theorem_iff`.
-/

import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.MvPowerSeries.Substitution
import ConciseIPRA.PR
import ConciseIPRA.BiInterpretation

noncomputable section

open scoped PowerSeries
open PowerSeries

namespace LagrangeInversionBlueprint

/-! ## Abstract formal-power-series layer -/

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- `g = X * phi(g)` with zero constant coefficient. -/
def IsLagrangeSolution (phi g : R⟦X⟧) : Prop :=
  PowerSeries.constantCoeff g = 0 ∧
    g = (PowerSeries.X : R⟦X⟧) * PowerSeries.subst g phi

/-- The alternative, denominator-free coefficient identity which is the best
first target in Mathlib.  The derivative notation in the intended statement is
`d⁄dX R phi`.

Target statement (schematic):

```
theorem lagrange_burmann_alternative
    {phi g H : R⟦X⟧} (hg : IsLagrangeSolution phi g) (n : ℕ) :
  coeff (n + 1) (subst g H) =
    coeff (n + 1)
      (H * phi ^ n * (phi - X * (d⁄dX R phi))) := by
  ...
```

Proof route:
* define finite Laurent polynomials and `residue`;
* prove `residue_derivative`;
* prove `residue_subst_mul_derivative` for a series of order one;
* apply it to `H(g(z)) z^(-n-2)` and `z = w / phi(w)`.
-/

/-- The integral Lagrange--Buermann identity.  Multiplying by `n+1` avoids a
field division and is the correct object-level theorem for arithmetization.

Target statement (schematic):

```
theorem lagrange_burmann_integral
    {phi g H : R⟦X⟧} (hg : IsLagrangeSolution phi g) (n : ℕ) :
  (n + 1 : R) * coeff (n + 1) (subst g H) =
    coeff n ((d⁄dX R H) * phi ^ (n + 1)) := by
  rw [lagrange_burmann_alternative hg]
  -- use `coeff_derivative`, `derivative_pow`, and the Leibniz rule
  ...
```
-/

/-- The special coefficient formula follows by taking `H = X`:

```
(n + 1 : R) * coeff (n + 1) g = coeff n (phi ^ (n + 1)).
```

Taking `H = X^k` gives the power form

```
(n : R) * coeff n (g^k) = (k : R) * coeff (n-k) (phi^n)
```

with the coefficient interpreted as zero when `n < k`.
-/

/-! ## Finite implementation -/

/-- A coefficient vector for `R[X]/(X^(N+1))`.  The executable development
should use this representation or the equivalent quotient by `X^(N+1)`.
Every operation below is a bounded fold, hence primitive recursive after the
coefficient ring is encoded. -/
abbrev TruncSeries (N : ℕ) (A : Type*) := Fin (N + 1) → A

/-- Congruence through degree `m-1`. -/
def AgreeBelow {N : ℕ} {A : Type*} (m : ℕ)
    (a b : TruncSeries N A) : Prop :=
  ∀ i : Fin (N + 1), i.1 < m → a i = b i

/-- Planned executable modules and their central lemmas.

`TruncatedSeries.lean`
* `tadd`, `tmul`, `tpow`, `tderiv`, `tcomp` as bounded `Finset` sums;
* coefficient equations and closure under truncation;
* primitive-recursive encodings over `ℤ`, `ℚ`, and Gaussian rationals.

`FixedPoint.lean`
* `step phi g = X * tcomp phi g`;
* `step_congr : AgreeBelow m a b -> AgreeBelow (m+1) (step phi a) (step phi b)`;
* `iterate_fixed` and `iterate_unique` after `N+1` steps.

`FormalResidue.lean`
* finite Laurent vectors with exponent interval `[-B,N]`;
* `residue_derivative = 0`;
* change of variables for `F=X*U`, proved first on Laurent monomials;
* only the finitely many exponents needed by the target coefficient occur.

`LagrangeBuermann.lean`
* the two coefficient identities and the inverse-series corollary.

`Bell.lean`, `Applications.lean`, `Good.lean`, `Puiseux.lean`
* finite Bell sums, examples, the multivariate determinant formula, and
  ramified inversion.
-/

/-! ## Object-theory compilation into ProveIt's iPRA -/

open LeanProofs.ConciseIPRA

/-- The final object theorem is a closed formula in `Fm PTm 0` asserting the
correctness of the primitive-recursive coefficient algorithms.  Its exact
syntax depends on the chosen tuple/list coding. -/
opaque lagrangeCorrectnessFormula : Fm PTm 0

/-- Target derivation in the ordinary first-order presentation of iPRA.
This is intentionally opaque in the blueprint; the completed development must
replace it by a term built from `PRA.precZero`, `PRA.precSucc`, arithmetic
lemmas, and `PRA.qfInd`. -/
opaque lagrangeCorrectnessPRA :
  Prf PRAAx [] lagrangeCorrectnessFormula

/-- The existing bridge transports the completed iPRA derivation to the
concise scalar theory `T_eq`.  This definition is already executable once the
preceding proof is supplied. -/
def lagrangeCorrectnessTeq :
    Prf TeqAx []
      (lagrangeCorrectnessFormula.map (fun _ => FromPRA.sigma)) :=
  (pra_theorem_iff lagrangeCorrectnessFormula).mp lagrangeCorrectnessPRA

/-! ## Quantifier-free induction invariant

For a requested truncation order `N`, encode a Boolean predicate saying that
all coefficient equations below the current stage hold.  The key invariant is

```
Inv(r) := all i < min(r,N+1), coeff(iterate step r 0,i)
          = lagrangeCoefficient(phi,i).
```

`all` is a primitive-recursive Boolean fold, so `Inv` is quantifier-free after
all algorithms have been named by `PR` symbols.  `PRA.qfInd` applies literally.
The same pattern proves the Bell and application identities after clearing all
nonzero integer denominators.
-/

end LagrangeInversionBlueprint
