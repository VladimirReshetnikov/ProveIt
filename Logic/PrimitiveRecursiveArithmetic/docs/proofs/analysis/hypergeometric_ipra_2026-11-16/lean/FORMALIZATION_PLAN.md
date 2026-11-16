# Lean and ProveIt formalization plan

## Status

The two `.lean` files in this archive are an **uncompiled outline**.  They are
not a completed proof and do not justify calling any analytic theorem
kernel-checked.  `HypergeometricFinite.lean` has ordinary definitions and a
small proved core, followed by an explicitly marked `Planned` namespace of
axiom declarations.  Each axiom is a target to eliminate.  No `sorry` is used.
`HypergeometricIPRA.lean` is an abstract migration ledger for the object theory.

## Repository integration point

The target repository library is `IPRADerivations` in namespace
`LeanProofs.IPRA`.  The ordinary object theory uses derivations of shape

```lean
([] : List (Fm PTm 0)) ⊢[PRAAx] φ
```

and `pra_iff_native` transports a completed result to the native scalar core.
The most relevant existing layers are:

1. `Core/Basic`, `Core/Semiring`, `Core/Integers`, `Core/Tactic`;
2. `Core/Definitions` for primitive recursion, finite sums/products, powers,
   and factorials;
3. `Core/BoundedSums`, `Core/SumLemmas`, `Core/MultiSums`;
4. `Core/Pairing` for simultaneous recursions;
5. `Core/Division`, `Core/Gcd`, `Core/Bezout` for rational normalization and
   denominator guards;
6. the Taylor/Cauchy and Gamma proof packets for effective analytic contracts;
7. `Analysis/FabiusFunction/Lean/FabiusFunction/ClassicalHypergeometricLimit.lean`
   for existing metatheoretic definitions of ordinary hypergeometric terms.

Import paths must be checked against the repository revision used for the
implementation; they are intentionally not guessed in the outline file.

## Proposed module graph

```text
SpecialFunctions/Hypergeometric/Codes
  -> Pochhammer
  -> Coefficients
       -> ODE
       -> Termination
       -> Contiguous
            -> FiniteContinuedFraction
       -> Transformations
       -> OrthogonalPolynomials
       -> CubicAndGlasser
  -> EffectiveNames
       -> DiskTail
       -> EulerIntegral
            -> Summations
       -> PathContinuation
            -> ConnectionFormula
            -> Kummer24
```

The finite subtree through `CubicAndGlasser` should be completed before the
analytic subtree is started.

## Concrete arithmetic representations

- Integer: sign bit plus magnitude, or the existing `ZT` difference terms.
- Rational: numerator plus positive denominator (`denPred + 1`), normalized by
  bounded gcd when canonical cancellation is needed.
- Complex rational: pair of rationals; use the `ℓ¹` norm for decidable bounds.
- Finite sequence: pairing or the existing bounded-sum symbol interface.
- Dyadic name: PR evaluator `X(q)` with the internal regularity theorem
  `2^(q+1) * ‖X(q+1)-X(q)‖₁ ≤ 1`.
- Apartness: a natural witness `k` for `2^-k ≤ |z|`.
- Branch certificate: finite polygon list plus logarithm name and cut margins.

Every division in an object-theory formula should be eliminated by cross
multiplication.  Nonzero hypotheses stay explicit; totalized division is only
an implementation device.

## Finite proof milestones

### 1. Rising factorial

Define `rise(a,0)=1`, `rise(a,n+1)=rise(a,n)(a+n)`.  Derive:

- product form;
- `rise(-m,n)=0` for `m<n`;
- multiplication/splitting `rise(a,m+n)=rise(a,m)rise(a+m,n)`;
- factorial identities `rise(1,n)=n!` and
  `rise(-m,n)=(-1)^n m!/(m-n)!` for `n≤m`, after clearing division.

The zero criterion uses a bounded Boolean fold and quantifier-free induction.

### 2. Hypergeometric coefficient

Store numerator and denominator separately:

```text
num(n) = rise(a,n) rise(b,n)
den(n) = rise(c,n) fact(n)
```

For rational parameters first clear all fixed denominators.  Prove the
cross-multiplied recurrence

```text
num(n+1) den(n) (c+n)(n+1)
 = num(n) den(n+1) (a+n)(b+n).
```

After normalizing the definitions, the proof is an `ipra_ring` goal.

### 3. Derivative and ODE

Formal derivative is coefficient shift `D u(n)=(n+1)u(n+1)`.  The derivative
identity follows from the coefficient recurrence.  The ODE residual at degree
`n` is exactly

```text
(n+1)(c+n)u(n+1) - (a+n)(b+n)u(n).
```

Represent signed equality with `ZT.eq`; no analytic differentiation occurs.

### 4. Formal uniqueness

If `u(0)=v(0)` and both satisfy the recurrence with apart denominator at every
index below `N`, simultaneous induction proves equality below `N`.  Encode
`∀j<N` as a bounded Boolean fold so that the induction formula is literally
quantifier-free.

### 5. Terminating identities

Prove Chu–Vandermonde by induction on the terminating degree.  Two viable
invariants are:

1. Pascal-style induction after extracting the last term;
2. coefficient comparison in `(1-x)^m (1-x)^{-b}`.

The first is likely shorter in the object theory.  Jacobi and Legendre
specializations then reduce to parameter substitution plus fixed factorial
identities.

### 6. Transformations

For Euler and Pfaff, avoid analytic substitution initially.  Define the right
side as a Cauchy product and prove its coefficient recurrence and constant
term.  Formal uniqueness identifies it with the left side.  Quadratic
transformations use the same approach with a finite composition operator; a
more economical implementation may verify that the algebraic pullback carries
the differential operator and then invoke recurrence uniqueness.

### 7. Contiguous relations and finite continued fraction

Normalize all fifteen contiguous relations to three generators.  Prove each
coefficient identity with `ipra_ring`.  Eliminate intermediate contiguous
functions over a finite list to obtain continuant recurrences `P_n,Q_n`.
The theorem should first be an exact finite identity; convergence of
`P_n/Q_n` is a later analytic contract.

### 8. Cubic and Glasser identities

For the cubic radical, define the coefficient sequence by recurrence from
`Y+x²Y³=1`.  Prove that the hypergeometric coefficients satisfy the same
recurrence and constant term.  This avoids formal radicals entirely.

For the Glasser family, define Fuss–Catalan coefficients and prove the finite
multinomial convolution yielding `y=1+f_k^k t y^(k+1)`.  The displayed radical
form is then a separate effective root-isolation theorem.

## Effective analysis milestones

### Disk convergence

Produce a polynomial cutoff `N0` such that the exact term ratio is bounded by
`r<1`.  The main induction invariant is

```text
∀j<N, 2^s * |T(N0+j)| ≤ A * R^j
```

in cleared integer form.  Combine it with the finite geometric identity and a
bounded-search cutoff.

### Euler integral

Reuse the finite-integration contract style of the Taylor/Cauchy packet:
endpoint truncation, a rational mesh on the central interval, and explicit
rounding allocation.  Prove the integral-series interchange only as a finite
head plus two independently bounded tails.

### Summations

Gauss summation in the Euler chamber follows by the beta identity.  Kummer,
Gauss second, and Bailey follow from a finite algebraic substitution plus
Gauss.  Each substitution needs an explicit Jacobian and endpoint-bound
certificate.

### Continuation and connection

Implement continuation along a supplied rational polygonal path by local ODE
Taylor steps.  Store local radius, derivative bounds, and error budgets in a
finite certificate.  The nonresonant connection formula is obtained by
matching two local bases at a rational overlap point.  Resonant logarithmic
cases should be separate modules, not hidden behind generic division by a
vanishing gamma factor.

## Audit discipline

For every completed object-theory theorem:

1. build the `IPRADerivations` target;
2. add a closed theorem to the aggregate module;
3. add `#print axioms theorem_name` to `Checks/Axioms.lean`;
4. require no `sorryAx` and no new analytic axiom;
5. record the exact repository commit and Lean/Mathlib versions;
6. only then change the corresponding inventory row from “outline” to
   “kernel-checked”.
