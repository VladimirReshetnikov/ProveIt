# Lean formalization roadmap and status

## Delivered status

`FiniteSkeleton.lean` is **uncompiled candidate source**, not a completed
formalization of either analytic theorem. It contains proof scripts for
finite rational telescoping, linearity, a triangle bound, propagation of
local derivative errors, and the alternating recurrence behind repeated
integration by parts. It also contains interface structures for regular
rational names. There are no `sorry` declarations or new axioms in that
file. Absence of such declarations is not a substitute for compilation.

The preparation environment had no `lean`, `lake`, or `elan` executable on
PATH, and no such executable was found in the inspected runtime locations.
The mathematical argument and exact Python checks are the completed parts
of this package; these Lean scripts require compilation and extension.

## Repository baseline

Inspected repository: `VladimirReshetnikov/ProveIt`.

Pinned commit: `0bf379a84212abd05e9a3f0b1320a3d7da509cf9`.

Toolchain: `leanprover/lean4:v4.32.0`.

Mathlib revision in the root `lakefile.toml`: `v4.32.0`.

The relevant deeply embedded foundations are under
`Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/`:

* `PR.lean`: arity-indexed primitive recursive syntax `PR`; number terms
  `PTm`; theory `PRAAx`; derived quantifier-free induction `PRA.qfInd`.
* `Deduction.lean` and `Syntax.lean`: intuitionistic natural deduction,
  formulas, substitution, and quantifier-free formulas.
* `BiInterpretation.lean`: `biInterp`, `pra_iff_teq`, and `teq_iff_pra`.
* `NativeBiInterpretation.lean`: `pra_iff_native` and `native_iff_pra`.

The namespace is `LeanProofs.ConciseIPRA`. In particular, the final goal is
an inhabitant of an object-theory derivability statement of the form

```lean
Γ ⊢[PRAAx] φ
```

where `Γ` contains the explicitly arithmetized regularity promises and `φ`
is the requested precision-indexed rational conclusion. The object theory
uses intuitionistic logic and quantifier-free induction. An arbitrary Lean
theorem about `ℝ`, `ℚ`, or functions is not an inhabitant of this type.

Permanent source URLs:

* https://github.com/VladimirReshetnikov/ProveIt/blob/0bf379a84212abd05e9a3f0b1320a3d7da509cf9/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean
* https://github.com/VladimirReshetnikov/ProveIt/blob/0bf379a84212abd05e9a3f0b1320a3d7da509cf9/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean
* https://github.com/VladimirReshetnikov/ProveIt/blob/0bf379a84212abd05e9a3f0b1320a3d7da509cf9/lean-toolchain
* https://github.com/VladimirReshetnikov/ProveIt/blob/0bf379a84212abd05e9a3f0b1320a3d7da509cf9/lakefile.toml

## Stage 1: compile the finite semantic prototype

Use a checkout of ProveIt at the pinned commit with its dependencies already
installed. From that checkout's root:

```text
lake env lean /absolute/path/to/FiniteSkeleton.lean
```

This checks only the finite semantic prototype. The file imports Mathlib
for rational arithmetic tactics; no real-analysis theorem is used. Inspect
the listed declarations with `#print axioms` after successful compilation.
Do not describe this step as an iPRA formalization.

The first derivative estimate to verify is exactly

```text
forall i < n, |F(i+1) - F(i) - h*f(i)| <= e
  implies
|F(n) - F(0) - h*sum(i<n, f(i))| <= n*e.
```

This is `finite_ftc_bound` in the candidate file. It is independent of
limits, differentiation, and completeness. Set `e = |h|*epsilon` when
applying a certified derivative estimate, adding the explicit rational
evaluation errors before invoking it.

The repeated-parts identity is `finite_parts_chain`. For arrays `I` and
`C`, its hypothesis is `I(r)=C(r)-I(r+1)`, and its conclusion is

```text
I(0) = sum(r<n, (-1)^r*C(r)) + (-1)^n*I(n).
```

The analytic argument supplies the single-cell identities. The finite
algebra determines all signs and endpoint corrections.

## Stage 2: represent the finite arithmetic in PRAAx

1. Encode signed integers and nonzero-denominator rationals as natural
   numbers. A denominator can be stored as `d+1`. Every comparison is a
   decidable signed-integer cross-product comparison. Intermediate pairs
   need not be reduced, but normalize rational arguments before passing
   them to an input evaluator. Bounded-gcd reduction is primitive recursive
   and makes equal shared grid nodes literally identical evaluator inputs.
2. Define the fixed primitive recursive symbols for pairs, finite lists,
   rational operations, powers of two, factorial, binomial coefficients,
   finite sums, and bounded maxima. Use `PR.comp` and `PR.prec` explicitly.
3. Prove their defining identities in `Prf PRAAx`. Introduce reusable
   macros that produce actual derivations of equality substitution,
   integer order facts, finite triangle inequalities, and finite sums.
4. Replace bounded quantifier notation in induction invariants by
   primitive recursive Boolean folds. A bounded formula written with
   `forall i<n` is not literally quantifier-free in the repository syntax;
   its Boolean encoding is what permits `PRA.qfInd`.
5. Construct deeply embedded proofs of the finite identities above for
   coded arrays. Keep all analytic hypotheses in the side context and use
   only rational, quantifier-free formulas as induction invariants.

This stage is work still to be done. A theorem about an arbitrary Lean
function `Nat -> Rat` does not perform any of these constructions.

## Stage 3: primitive recursive names and rational integration

For each fixed input evaluator, its modulus, and its bounds, construct the
output evaluator by composition and bounded loops exactly as in the
manuscript. The ambient Lean structures in `FiniteSkeleton.lean` record the
shape of the promises, but they allow arbitrary Lean functions. The deep
embedding must instead use concrete fixed `PR` expressions.

There is no primitive recursive universal evaluator of all primitive
recursive programs. Accordingly, the theorem is an externally uniform
schema in fixed primitive recursive definitions. Numerical parameters and
precision indices remain ordinary number variables. One must not quantify
over arbitrary program codes and silently evaluate them by a new primitive
recursive function.

For integration, prove finite common-refinement estimates first. Express
the output name's Cauchy property and the comparison of any sufficiently
fine rational sum with that name as rational precision inequalities.
Prove additivity by splitting finite sums at a rational endpoint. All
limits in the manuscript abbreviate these verified inequalities.

## Stage 4: FTC I and FTC II

FTC I: construct the integral-name evaluator. Compare its increment over
`[x,x+h]` with `h*f(x)` using the supplied continuity modulus. For a
nonzero quotient, retain the rational apartness/positive lower-bound
witness needed to divide by `h`; do not decide whether an arbitrary real
name is zero.

FTC II: the input includes a uniform first-order remainder modulus, as
specified in the manuscript. Specialize `finite_ftc_bound` to a fine
rational grid, include all approximation errors, and telescope. No mean
value theorem, compactness theorem, or attainment of an extremum is
needed. Proving that a conventional classical `C^1` hypothesis supplies
these data is a separate stronger metatheoretic correspondence statement,
not an unmentioned step inside iPRA.

Prove integration by parts from the corresponding finite product
increment identity and the same error accounting, or use the manuscript's
explicitly certified product rule followed by FTC II.

For the separate Riemann-integrable FTC II in the manuscript, formalize
the supplied finite tagged-partition realizer `P(k)` as a fixed primitive
recursive function. Its correctness hypotheses are: validity of the
ordered rational partition and its tags, mesh at most `2^(-rho(k))`, and
both distances from a tag to its cell endpoints at most
`2^(-nu(tag,k))`. Keep the tagged-sum Cauchy promise (R) and the pointwise
linearization promise (PD) in the side context. Apply (PD) twice per cell,
cancel the repeated tag evaluation, and then telescope to prove

```text
|H(b,p) - H(a,p) - S(P(k),p)|
  <= L*2^(-k) + (4*N+L)*2^(-p),
```

where `N` is the number of cells returned by the already computed `P(k)`.
The tagged-sum comparison and endpoint radii give the final error
`(L+1)*2^(-k) + (4*N+2*L+2)*2^(-p)`. For target index `r`, use
`k=r+sigma(L+1)+4` and `p=r+sigma(4*N+2*L+2)+4`, with `sigma` as in the
manuscript. This retains primitive recursiveness even when the partition
size depends on `k`. Do not infer the partition realizer from a qualitative
Cousin lemma or compactness, and do not infer properties of an arbitrary
discontinuous real extension from rational samples alone.

## Stage 5: Bernoulli polynomials and Euler--Maclaurin

1. Compute the finite Bernoulli table by its rational triangular recurrence.
   Use a coded list accumulator for course-of-values references.
2. Prove the derivative, endpoint, and reflection identities by equality of
   finite polynomial coefficient arrays. No infinite generating series is
   needed. Odd Bernoulli-number vanishing above index one follows from
   reflection plus endpoint equality.
3. On each unit cell, derive the first sawtooth integration-by-parts
   identity. Treat the first periodic Bernoulli function cell by cell; no
   uniform-continuity claim across its integer jumps is permitted.
4. Apply the finite alternating recurrence and sum over the finitely many
   cells. Use the shared endpoint values for orders at least two and the
   odd-term cancellation to obtain the usual even corrections.
5. Formalize the Bernstein coefficient certificate for the normalized
   polynomials `P_n = B_n/n!`. If `b_i` are the degree-`n-1` coefficients,
   define the degree-`n` coefficients by the exact finite recurrence

   ```text
   d_j = (sum(i<j, (i+1)*b_i) - sum(j<=i<n, (n-i)*b_i)) / (n*(n+1)).
   ```

   The sum of the absolute rational weights is
   `(j*(j+1)+(n-j)*(n-j+1))/(2*n*(n+1)) <= 1/2`. Prove this algebraically
   for `n>=1` and `j<=n`; induction on the finite maximum coefficient
   gives `max_i |b_i| <= 2^(-n)` at order `n`. Prove the finite Bernstein
   basis is nonnegative and sums to one on `[0,1]`, obtaining
   `|P_n(t)| <= 2^(-n)`. The invariant is a coded finite maximum and
   polynomial-list equality, not a quantified statement about all real
   points. Together with the supplied highest-derivative bound this gives
   the manuscript's elementary remainder bound, with no assertion that
   the infinite Euler--Maclaurin series converges.

The manuscript supplies the fully rational accumulator in its section
"A fully rational Euler--Maclaurin certificate". For `L>=1`, order `r>=1`,
and a common integer bound `M>=1`, put

```text
C = 2^r,
D = 2^r*(M+1)*(r+1)^2,
q = n + sigma(8*(L+1)*(r+1)*D),
ell = max(q, mu_0(q), mu_r(q), nu_0(q), ..., nu_(r-1)(q)),
H = 2^ell, h = 2^(-ell), p = q+ell+4.
```

Use this same rational evaluation precision `p` at every repeated grid
endpoint. Define rational quadratures `Q_j` and rational endpoint terms
`b_j` exactly as in the manuscript, and define
`E_j=b_j-Q_(j-1)-Q_j`. Prove the local product defect bound first, then
sum to obtain `|E_j| <= L*D*2^(-q)`. The exact rational identity is

```text
b_1 = Q_0 + sum(2<=j<=r, (-1)^j*b_j) + (-1)^(r+1)*Q_r
      + sum(1<=j<=r, (-1)^(j+1)*E_j).
```

The central rational residual is consequently at most `L*r*D*2^(-q)`.
After the separately proved quadrature and sample comparisons, the full
represented residual is less than `8*L*r*D*2^(-q) < 2^(-n)`. The cases
of zero interval length and zero recurrence length are handled before
these positive-length schedules.

If the truncation order is a number variable, the input derivative family
must itself have one fixed PR evaluator with the derivative index as an
argument, and supplied PR bounds/moduli. Fix `n` first and prove the
displayed finite accumulator identity and inequality with quantifier-free
induction; only afterward universally generalize `n`. Do not induct over
order using equality of real names as the induction formula: that
equality expands to a universally quantified precision statement and is
not quantifier-free.

## Stage 6: transfer to the native scalar presentation

Only after constructing the object-theory derivations apply
`pra_iff_native` from `NativeBiInterpretation.lean`. This transfers each
arithmetized result to the native scalar calculus and preserves the
declared side assumptions. The existing bi-interpretation performs no
automatic proof extraction from ambient Lean analysis.

The native-core theorem is optional if the desired final statement is
already a derivation in the conventional iPRA presentation `PRAAx`.

## Inspected prior work and dependency boundary

At the pinned commit, `docs/drafts` contained the archives `FTA_iPRA.zip`,
`basel_ipra.zip`, `isoperimetric_ipra.zip`, `minkowski_ipra.zip`,
`pnt_ipra_constructive_2026-11-14.zip`, and `stirling_ipra.zip`.
The directory listing was inspected. These binary archives were not used
as proof dependencies; this package does not claim an audit of their
contents.

An existing relevant formal theorem is
`LeanProofs.IntegerPoints.EM.sum_eq_integral` in
`NumberTheory/IntegerPoints/Lean/IntegerPoints/EulerMaclaurin.lean`:

https://github.com/VladimirReshetnikov/ProveIt/blob/0bf379a84212abd05e9a3f0b1320a3d7da509cf9/NumberTheory/IntegerPoints/Lean/IntegerPoints/EulerMaclaurin.lean

It proves the first-order sawtooth formula for real inputs and complex
values. Its implementation uses `HasDerivAt`, `Continuous`, interval
integrals, measure theory, real floor, and compactness to obtain a bound.
It is a useful independent check on signs and endpoint conventions. It is
not an admissible iPRA lemma merely because it is in the same repository,
and it is not imported by the proposed arithmetic proof.

The target is a complete mathematical proof with a precise route to a
deep formalization. This roadmap records the remaining formalization work
openly and does not present that work as already checked.
