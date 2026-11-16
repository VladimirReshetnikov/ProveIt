# Lean completion roadmap

## Baseline

The intended target is the `ProveIt` repository snapshot and Mathlib version
recorded in `../SOURCES.md`.  `lakefile.toml` pins Mathlib `v4.32.0`.
The relevant existing interfaces are:

- `PowerSeries.subst`, `PowerSeries.HasSubst`, `coeff_subst`,
  `substInv`, and the left/right inverse lemmas;
- `PowerSeries.derivative`, `coeff_derivative`, `derivative_pow`, and
  `derivative_subst`;
- `MvPowerSeries.subst` for Good's multivariate formula;
- `ConciseIPRA.PR`: `PR`, `PTm`, `PRAAx`, `PRA.precZero`,
  `PRA.precSucc`, and `PRA.qfInd`;
- `ConciseIPRA.BiInterpretation.pra_theorem_iff` for transport to `T_eq`.

## Phase 1: finite algebra, independently executable

Create `TruncatedSeries.lean` with

```lean
abbrev TruncSeries (N : Nat) (R : Type u) := Fin (N+1) -> R
```

and define Cauchy product, powers, derivative, and composition by bounded
`Finset` sums.  Prove coefficient equations by extensionality and `Finset`
reindexing.  This layer should use no topology and no classical choice.

Create `FixedPoint.lean`.  Define

```lean
step phi g := X * compose phi g
```

and prove that agreement below degree `m` is improved to agreement below
`m+1`.  Iterating from zero `N+1` times gives the unique solution of
`g = X*phi(g)` modulo `X^(N+1)`.

## Phase 2: finite residue proof

Use a finite Laurent-vector type whose supported exponent interval is explicit.
Prove:

1. the residue of a formal derivative is zero;
2. `Res (Q(F) * F') = Res Q` when `F=X*U` and `U(0)` is a unit;
3. the second result first for a Laurent monomial and then by a finite sum.

The monomial `X^-1` case is `F'/F = X^-1 + U'/U`; all other cases are formal
derivatives.  This is the only change-of-variables lemma needed.

## Phase 3: abstract Mathlib theorem

Lift the finite identity to `PowerSeries R` by coefficient extensionality.
The preferred first theorem is

```text
coeff (n+1) (H.subst g)
 = coeff (n+1) (H * phi^n * (phi - X * derivative phi)).
```

It avoids division by `n+1`.  Derive the usual form after multiplying by
`n+1`, using `coeff_derivative`, `derivative_pow`, and Leibniz.  Specialize to
`H=X`, `H=X^k`, and to `g = substInv F` after proving
`phi = X/F` and the fixed-point equation.

## Phase 4: finite corollaries

- `Bell.lean`: define exponential partial Bell polynomials as a bounded sum
  over multiplicity vectors.  Expand `(1+A)^(-n)` only to the requested degree.
- `Applications.lean`: algebraic equation, Lambert W coefficients, shifted W,
  and Catalan numbers.
- `Associahedron.lean`: define plane rooted trees and prove the signed-tree
  inverse formula; connect trees with faces only after fixing a convention for
  associahedron indices.
- `Good.lean`: multivariate Laurent residue and the logarithmic Jacobian
  determinant.  Start at fixed dimension `d`, then generalize the determinant
  to a coded finite matrix.
- `Puiseux.lean`: formal binomial roots and the substitution `z=t^m`.

## Phase 5: iPRA object derivations

Encode integers, rationals, finite vectors, and matrices by natural numbers.
All loops in Phases 1, 2, and 4 are bounded folds or primitive recursions, so
name them with `PR` symbols.  Clear rational denominators before stating the
closed correctness formula.

Turn every bounded universal condition into a Boolean `all` fold.  The
fixed-point stabilization proof then has a literally quantifier-free invariant,
allowing direct use of `PRA.qfInd`.  Build a term

```lean
Prf PRAAx [] lagrangeCorrectnessFormula
```

and transport it with

```lean
(pra_theorem_iff lagrangeCorrectnessFormula).mp proof
```

## Phase 6: constructive analytic lifting

Reuse the regular-name and modulus conventions of the existing Taylor/Cauchy
packet.  Formalize the explicit contraction constants in the paper.  No
compactness or choice is required: Picard iteration has the primitive-recursive
error bound `rho * 2^(-m)`.  The exact shifted-Lambert radius additionally needs
an effective complex-continuation certificate; it should be kept in a separate
module so the algebraic core does not depend on it.

## Validation status

`LagrangeInversionBlueprint.lean` is a detailed target file, not a completed
kernel-checked proof.  `../code/verify.py` is executable and was run with exact
rational arithmetic; its output is in `../validation/validation_output.txt`.
