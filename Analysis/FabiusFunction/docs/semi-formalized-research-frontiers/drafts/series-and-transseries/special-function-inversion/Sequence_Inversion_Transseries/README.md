# Asymptotic Transseries and Inversion of Eight Sequences and Special Functions

**Canonical consolidation of twenty-four filed articles**, made on 3 September
2026. `sequence_inversion_transseries.tex` (205 A4 pages) and the PDF built
from it in the same run.

## What it is

Eight subjects are developed to all orders and then inverted:

| Chapter | Subject | Core | Notes |
| --- | --- | --- | --- |
| 1 | rooted trees, A000081 | `aX + b log X` | `a = log(1/ρ)`, `b = −3/2`, `α = 1` |
| 2 | double factorial, A006882 | `X(κ log X + d)` | *not* an exponential–power model |
| 3 | partitions, A000041 | `aX + b log X` | `a = π√(2/3)`, `b = −1`, `α = 1/2` |
| 4 | swing factorial, A056040 | `aX + b log X` | `a = log 2`, `b = σ/2` |
| 5 | Gamma and Barnes `G` | `a x^p (log x − β)` | `p = 1, 2`; a **second** core |
| 6 | hyperfactorial `K` | `a x^p (log x − β)` | `p = 2`; one resonant logarithm |
| 7 | subfactorial `!n` | `Γ(x+1)/e` | borrows its carrier from Chapter 5 |
| 8 | real-argument Fibonacci | `e^{λx}` | no Lambert core; **converges** |

Chapters 1–4 are sequences with the `aX + b log X` core that Chapter 0
inverts. Chapters 5–6 need a different block — `a x^p (log x − β)`, where the
unknown *multiplies* the logarithm — proved in Chapter 5 in the generality
`a x^p (log x − β)^r`. Chapters 7–8 are the boundary cases: one whose
dominant block belongs to another chapter, and one the frame does not cover.

Chapter 0 states the shared apparatus **once** — the exponential–power model
and the axiomatized dominant core, ordinary and exponential partial Bell
polynomials, Lagrange–Bürmann and the Lagrange fixed-point formula, perturbed
inversion around an exactly invertible core in both its analytic and its
formal-jet form, the exact Lambert carrier and the branch rule, the all-orders
reversion, the flattening into a polynomial–logarithmic transseries, the three
inverse objects of a discrete sequence with the staircase theorem, backward
error as a certificate, remainder transport, and optimal truncation. Chapters
1–8 cite it 266 times and restate none of its proofs.

## Why one volume

Twenty-four articles carried twenty-four copies of that apparatus. The second
twelve were written without knowledge of the first twelve and converged on it
independently — which is the strongest evidence that consolidating was worth
doing. Measured duplication among the second twelve alone: the single Gamma
inverse block `d₅` is printed in **seven** of them; eight state a general
triangular inversion theorem; seven state a residual-to-error transfer; seven
prove a Lagrange–Bürmann reversion.

Facts only visible from the merged view, none of them in any source:

* **Four square roots are one lemma.** `√(Λ²T²+1/12)`, `√(λ²U²−2αU)`,
  `√(U²+1/6)` and `√(ρ²+1/12)` all come from truncating the normalized
  equation to its linear and quadratic terms plus the lowest forcing monomial.
  Which *extraction* of the coefficient family that quadratic computes — the
  deepest pole in the slope, or the coefficientwise large-slope limit — is
  decided by whether the forcing monomial is resonant. Resonance and pole
  depth are two readings of one quadratic.
* **The slope-denominator bound is attained.** The deepest pole of the Gamma
  blocks is exactly `binom(1/2,n)·12^{−n}`, and of the Barnes blocks
  `binom(1/2,n)·(−2α)^n`.
* **Acceleration is resummation.** The K-function's "accelerated coordinate"
  `T = x²−x+1/6` is the resummation of its own resonant subsector. The
  absorption lemma behind it applies to Barnes `G` too, which no Barnes source
  attempted.
* **One Bernoulli value, two jobs.** The `1/12` appearing as the Gamma deepest
  pole and as the K resonant limit is `−2·B₂(1/2)/2` both times — once as a
  tail coefficient, once as a logarithmic coefficient.
* The partition numbers are the `α = 1/2` case, not an exception; and the two
  "factorials" are not the same kind of object.

## Corrections to the sources

Appendix B lists every repair; the boxed corrections appear in the text where
they occur. The most consequential:

* **A proof that does not apply, in five of the first twelve articles.** The
  Lagrange fixed-point formula is derived by introducing a marker and applying
  Lagrange–Bürmann, which requires `φ(0)` invertible; here `φ(0) ∈ tR[[t]]` is
  a non-unit and the residue argument breaks. The identity is true and is
  proved here by universality. Every reversion in the volume depends on it.
* **An existence claim no source makes effective.** All six power–logarithmic
  sources justify the eventual inverse of Barnes `G` and of `K` with
  "`(log G)' ~ x log x`, hence increasing for sufficiently large `x`" — true,
  ineffective, and every numerical table in all six evaluates inside the range
  their own justification does not cover. Explicit thresholds are proved.
* A triangular-inversion theorem stated under local finiteness of the support
  semigroup, strictly stronger than the proof uses; well-ordering suffices, by
  Neumann's lemma.
* A coefficientwise limit presented as a "resummation" while the next remark
  says it is not; the accurate statement, and the coordinate change that does
  make it one, are both given.
* A divergent operator series printed as an equality after setting its
  bookkeeping coupling to `1`.
* A Rademacher amplitude whose definition returns `cos(2πν)` instead of `1` at
  `k = 1`, contradicting its own use and its article's monotonicity claim.
* `g(z) ≤ z²/3` on `[0,1]`, false at `z = 1` where `g(1) = e⁻¹ > 1/3`.
* `N_*(y) = ν(y) + o(1)`: no continuous function approximates a staircase
  uniformly; the gap is at least `1/2`.

Every printed coefficient, table and decimal in all twenty-four sources was
recomputed — in exact arithmetic where the quantity is exact, and to 50–220
digits where a numeric table was involved — by implementations independent of
the sources. **All of it reproduced except in one place**: one article prints
the constants of the inherited `−√ρ` sector to forty digits of which only
about twenty-five are correct, and its audit appendix reports a `D₃` that
contradicts its own main text. Both are corrected in Chapter 1, which prints
only digits it has verified. With that exception, no source contained an
arithmetic error, and every other defect found is in a statement, a
hypothesis, or a formal-versus-analytic conflation.

The second wave's verification totals: 67 exact identities for Gamma/Barnes,
36 for the K-function, 17 for the subfactorial and 16 for Fibonacci, all
passing; the nine high-precision inverse roots one source prints agree to all
25 digits displayed; `K(5) = 27648 = 1¹2²3³4⁴` and `F(n) = Fₙ` confirm the
special-function evaluations; and every error table was recomputed rather than
copied.

## Status

235 named results, 230 with proofs in the text; of the five without a `proof`
environment, four are corollaries whose derivation is displayed inline and one
is the Rademacher formula, quoted as the volume's single external analytic
input. 1,315 labels, no duplicates, no dangling references, no LaTeX errors,
no undefined references.

Comparison against the wider corpus, numerical reproduction beyond what is
recorded here, and Lean crosswalking are **not** done and are deliberately
left open; see the end of the synthesis chapter.

## Provenance

The twenty-four sources are listed in Appendix A with their line and page
counts. They were filed in this repository earlier the same day and are not
deleted by this consolidation; a residue audit and deletion is a separate,
later step.
