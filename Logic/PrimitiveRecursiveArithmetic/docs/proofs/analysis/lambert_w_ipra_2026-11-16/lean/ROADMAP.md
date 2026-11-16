# Lean completion roadmap

The two `.lean` files are **uncompiled blueprints**. They contain explicit
`sorry` obligations and introduce no user-defined axioms. A Lean executable was
not available in the artifact environment, so no build claim is made.

## Target environment

- ProveIt root toolchain: Lean and Mathlib v4.32.0 at the inspected revision.
- Import: `ConciseIPRA.NativeBiInterpretation`.
- Existing object-language interfaces: `PR`, `PTm`, `PRAAx`, `Prf`,
  `PRA.qfInd`.
- Existing bridge: `NFm.ofPRA`, `pra_iff_native`.

## Recommended modules

1. `LambertW/Code.lean` — signed integers, rationals, vectors, intervals.
2. `LambertW/BoundedFold.lean` — sums, products, Boolean folds, argmin search.
3. `LambertW/Rapid.lean` — rapid dyadic/rational names, extensional equality,
   apartness, arithmetic.
4. `LambertW/ExpLog.lean` — factorial/atanh series and explicit tail moduli.
5. `LambertW/BranchSearch.lean` — real branch brackets and bisection.
6. `LambertW/TruncSeries.lean` — Cauchy product, composition, derivative,
   truncated exponential.
7. `LambertW/Lagrange.lean` — finite residue change of variables and
   Lagrange–Bürmann.
8. `LambertW/Coefficients.lean` — Lambert and power-series coefficients.
9. `LambertW/Calculus.lean` — derivative polynomial recurrence and guarded
   identities.
10. `LambertW/Puiseux.lean` and `LambertW/Asymptotic.lean` — finite recursions
    plus explicit residual bounds.
11. `LambertW/Bounds.lean` — elementary logarithm/exponential inequalities.
12. `LambertW/Numerics.lean` — interval Newton/Halley and error certificates.
13. `LambertW/Object.lean` — encode each bounded invariant as `Fm PTm n`, prove
    it with `PRA.qfInd`, then transfer with `pra_iff_native`.

## First kernel-checked milestone

The best first milestone is the finite theorem

```text
W_N(X) exp(W_N(X)) = X mod X^(N+1),
W_N(X) = sum_{1 <= n <= N} (-n)^(n-1) X^n/n!.
```

It requires no completed-real infrastructure. After the vector operations are
coded, the invariant is a bounded conjunction of rational equalities, hence
quantifier-free. This isolates the central Lambert coefficient theorem as a
literal iPRA derivation before the analytic lifting is attempted.
