# Surcomplex Dynamics: Linearization Thresholds, Periods, and Normal Forms

**A merged research report, 106 pages.** Everything in this directory other
than `article.tex`, `article.pdf` and this README is preserved source
material.

```
article.tex   the merged report, standalone LaTeX with an internal bibliography
article.pdf   the compiled 106-page report
README.md     this guide
sources/      the six source manuscripts, unmodified, with their READMEs and audits
code/         the six source verification programs, unmodified
data/         the six recorded verification and build records, unmodified
```

## What the report is

Six independently written manuscripts, all dated 21 September 2026 and all
written against the same pinned repository snapshot
(`39f2be6667ade51bca2b45daa47e289d69c09764`), developed local and global
dynamics over complex Hahn fields `K = C((t^Gamma))` realized inside
`No[i]`, with `Gamma` a set-sized ordered abelian group of **arbitrary
valuation rank**. This report is their **union**, not a selection from
them.

They share one body of machinery — the set-sized workspace, strong
summability by well-ordered support plus local finiteness, Neumann's
positive-support lemma in finite-word form, halo evaluation by
coefficientwise double Taylor sums, Taylor substitution and its
near-identity inverse — and each of the six states that machinery from
scratch. Between 45 and 55 per cent of the combined text was the same
theory. The support lemma appears in all six.

## Read Section 2 first: the notion table

Four **inequivalent** conditions travelled under the single word
*resonance* across these six manuscripts, and five under the words *small
divisor*; worse, two groups of sources used the word *radius* with
**opposite monotonicity**. Unifying the notation without separating the
notions would have produced statements that read correctly and are false.
Section 2 therefore gives each variant its own name and symbol, and every
threshold statement in the report names which variant its hypothesis uses
and in which coefficient category it holds. Section 2.5 is a
theorem-by-theorem tag ledger.

**The four resonances.**

| Tag | Condition | Whose hypothesis it is |
|---|---|---|
| `RES_q` residue-resonant | `lambda` is **never** a root of unity, but its residue has exact finite order `q` | the exact finite-return ball, shell cycles, phase diagram, coherent lifting |
| `MR` / `NR` multiplier-resonant | `lambda^alpha = lambda_j` for some `|alpha| >= 2` | the five-row classification and everything built on the homological operator |
| `FR` frequency-resonant | `omega . k = 0` for some nonzero integer vector | the Hamiltonian package |
| `PAR` parabolic | leading multiplier exactly `1`, perturbed infinitesimally | the algebraicity/monodromy and the period/moduli sections — **with no divisor hypothesis anywhere** |

**The five small-divisor notions.** `SD_0` (support only, no arithmetic
condition at all); `SD_dr` (the rate `sigma`, **requiring multiplier
drift**); `SD_ex` (the rate `tau`, multiplier **exact**); `SD_fr` (the
frequency growth `Theta`); and `SD_none` (no condition, and no divisor
family to impose one on).

**The two radii.** Valuation balls `B_r = {v(z) > r}` and valuation
polydisks `D_rho` **shrink** as the threshold grows; ordinary disks and
polydisks `D_R` **grow** as `R` grows. Section 2.4 tabulates both, and the
report warns that a treatment using the decreasing-support Conway
convention has every inequality here reversed.

## Which archive contributed what

| Source in `sources/` | Contribution that survives here |
|---|---|
| `01-exact-resonant-return-threshold` | The exact maximal centered valuation ball read off the **finite `q`-th return iterate** rather than off `f` (§8), with the tuned cubic whose factorization `z^5(z^2-2z+2)(z^2-z+2)` moves the threshold from `delta/2` to `delta/4`; the resonant shell theorem with `P(alpha X) = P(X)`, the cycle count and `res(((f^oq)'(p_a)-1)/c) = a P'(a)`; the two-parameter phase diagram `r = max{(delta-sigma)/2, delta/4}` with its three shell polynomials and three leading coordinates (§12); the rank>1 witness that coefficient-valuation bounds are insufficient; the explicit rank-2 `Gamma = Q + Q*Omega` example; the strongly-Hahn-evaluable-but-not-coherent proposition; the return-face stability certificate |
| `02-radius-collapse-trichotomy` | The exact radius law `rad(h_{k,1}) = R exp(-(k+1) sigma)` (§7) and the highest-reciprocal-pole non-cancellation estimate that produces the factor `k+1`; the `Gamma_* = Q + sqrt2 Q` two-independent-exponent design and the explicit refusal to replace `v` by a power of `u`; the trichotomy `CD iff sigma=0`, `CG iff sigma<infinity`, which settles source 03's open question **in the drifted category**; the multiplicative-detuning several-variable version; the critical-scale representability test |
| `03-sharp-small-divisor-thresholds` | **Base of the merge.** The five-row coefficient-category table with per-row necessity witnessed at a single exponent `t^eta` (§6); `tau` and `tau = limsup (log q_{k+1})/q_k` with an explicit non-Brjuno `tau = 0` rotation; exp/log on `G_+(U)` for arbitrary open `U` with no shrinking; the flow law, admissible Hahn times and unique `n`-th roots; fixed-point ideals and their iteration invariance; the centralizer; the finite-order resonant splitting by cyclic averaging; the word-depth radius and degree certificates; workspace invariance with the recorded exception that the centralizer can grow; the two open questions |
| `04-algebraicity-dichotomy-and-monodromy` | The base field `B = C(w)((t^Gamma))` with **arbitrary rational-function** coefficients, not `K(w)`, and the algebraicity dichotomy (algebraic iff `deg V = 1`); the exact `rho_a = Log(1+mu eps)/Log(1+V'(a) eps)` obtained from `A'(a) = Log F'(a)` rather than from a truncated vector field; the torsion lemma and the resulting finite-cover obstruction; the classification of algebraic `h_0` together with the fact that `h_1` is then already transcendental; the sharp disk `v(z) > delta/q` with its **two distinct** failure mechanisms; the all-orders factorization `w(1+w^q)^{rho_q}` |
| `05-common-domain-period-moduli` | The ordinary coefficientwise period of `Omega_F = dz/W_F` as a **complete** conjugacy invariant on a stratum, with a unique basepoint-fixing conjugator; the explicit moduli space, periods giving a bijection onto `m_K^r` on an `r`-punctured plane; the exact five-term difference sequence with cokernel `K^r` and its explicit right inverse; the implicit displacement lemma (where the nowhere-zero hypothesis does its work); the flat/invisible-moduli theorem for `J_delta` nonzero with its `Gamma = Q + Q*omega` instance; the slow-time common-chart lifting theorem; the exact iterative residue `(p+1)/2` |
| `06-hahn-normal-form-thresholds` | The entire Hamiltonian chapter (§15): the gauge-normalized symplectic normal form on the whole finite phase space with **no arithmetic bound**; `Theta(omega)` and the sharp homological criterion; commuting actions, and every coherent first integral an entire-coefficient function of them; the coefficientwise holomorphic flow for ordinary complex time; the super-Liouville entire obstruction; the monomial support-and-degree certificate reaching valuation polydisks of **infinite** radius, with separate failure examples for positivity, well-ordering and finite fibers, and the sharp cubic boundary; the multiscale worked example |

## What was deduplicated, and what was kept twice

Printed **once**: the positive-support lemma (all six state it; sources 02,
03 and 05 each proved the underlying word order by the same
minimal-bad-sequence argument, and one copy is in Appendix A); strong
summability; the `t^gamma = omega^{-gamma}` workspace embedding; halo
evaluation; the coefficient-ring taxonomy; the one-variable centralizer
(sources 03 and 05 state it with the same hypotheses, the same conclusion,
the same meromorphic-ratio proof and the same remark that zeros of `a` need
not be removed); the continued-fraction formula for the divisor rate; the
leading-coefficient exponential integral `h_0 = w exp int (mu/V_0 - 1/w)`
(source 01's `H_0` with `V_0 = X P(X)` and source 04's with `V_0 = V` are
the same formula by the same transfinite variation-of-constants recursion);
the degree-six iterative logarithm of `z + t z^2`, which sources 03 and 05
each compute; and the quadratic Schröder recursion, which four sources
compute in four normalizations, printed once with the translation between
them.

Kept **twice or more, explicitly marked**, because the routes carry
different resources:

- three routes to a support-controlled linearizer — an operator geometric
  series (which is what yields the word-depth bound and hence the radius
  and degree certificates), an exponent-by-exponent well-founded recursion
  (which is what accommodates multiplier **drift**), and a Taylor-degree
  recurrence with a pre-cancelled infinitesimal divisor (which is what
  makes the finite-return threshold exact);
- two routes to iteration invariance of fixed-point data — an explicit
  invertible matrix giving **ideal** equality, and unique `n`-th roots
  giving **torsion-freeness** of the group; neither statement follows from
  the other;
- two routes to transcendence in the algebraicity dichotomy — a growth
  bound for algebraic functions (needed for **multiple** zeros) and an
  infinite monodromy orbit (needed for **simple** zeros); the source
  itself states they do not substitute for one another;
- both instantiations of the leading-coefficient formula, since the shell
  polynomial `P` is not available under `PAR` and the global factorization
  of `V` is not available under `RES_q`.

## The one conflict across the sources, and how it is resolved

Source 03 poses as **open** whether the common-domain germ category fails
for an intermediate divisor rate, proving only a word-depth lower bound and
stating explicitly that this does **not** prove radius collapse. Source 02
proves outright **failure**, with the exact law
`rad(h_{k,1}) = R exp(-(k+1) sigma)`.

This is not a contradiction, and each source says so. Source 02's negative
direction **requires** multiplier drift `F'(0) = lambda + u` and two
rationally independent positive exponents, both of which source 03
excludes: its multiplier is *exactly* `Lambda`, with no infinitesimal
linear part at any Hahn exponent. The report therefore prints source 02's
theorem as the answer **in the drifted category**, where it settles the
question negatively, and keeps the question **open for the fixed-multiplier
category**; source 02 itself records that eliminating drift removes the
reciprocal-jet mechanism. The two are not averaged into a single
"intermediate case" claim, and the exact radius law is never quoted without
its drift hypothesis (Warnings 2.6 and 7.11).

## What is NOT claimed

Section 22 is the consolidated record: **70 numbered items covering the 68
distinct limitations stated by the six sources**, distributed
11/9/10/14/12/12 across sources 01–06, each with its originating source
named. None was merged away or softened. The load-bearing ones:

- **Status.** Six AI-assisted, unrefereed research drafts; the merged
  report is likewise not refereed and not proof-assistant verified. **No
  Lean or other formal development corresponds to any theorem here.**
  Priority is not certified for any statement and no named published
  conjecture is claimed solved. Every repository and literature inspection
  was *targeted*, not exhaustive.
- **The exact ball is a valuation ball.** "Exact" means the maximal
  *centered valuation ball* only — not the full pointwise summability
  locus, not a maximal non-ball invariant domain, not every analytic
  continuation. The bounding shell is an algebraic valuation shell, **not**
  a topological boundary (valuation balls are clopen) and **not** a circle
  for the ordered-surreal modulus, and the common-domain disk is **not**
  identified with the valuation ball.
- **Equal characteristic zero is a genuine hypothesis.** The divisor
  cancellation leaves a factor `n-1` in the denominator, a valuation unit
  here and not in mixed characteristic. The finite-return formula and the
  shell-periodicity conclusion must **not** be transported to `C_p`; the
  source cites `p`-adic examples whose bounding sphere carries no periodic
  point at all.
- **No uniform bounds anywhere.** No uniform ordinary norm bound on any
  coefficient family, no norm, no Gevrey or weighted estimates, no ordinary
  holomorphic dependence on `t` near `t = 0`, no fixed real-valued norm and
  no sequential completeness. All control is by supports.
- **Negative results are category-relative.** They concern analyticity of
  the ordinary coefficient *functions on neighborhoods*. The
  formal-coefficient conjugacy always exists under nonresonance and can be
  evaluated on the infinitesimal monad; failure in one specified analytic
  category prohibits no set-theoretic conjugacy.
- **No global, all-scale or topological claims.** No global conjugacy on
  all of `No[i]`, no surreal-time flow, no class-sized analytic
  construction, no global analytic atlas, no contour theory on the fine
  topology, no fine-topologically continuous complex-time flow, and no
  coherence between arbitrary infinite-scale charts. Four *different*
  critical-scale obstructions are collected in §17 precisely so they
  are not mistaken for one.
- **"Transcendental" and "analytic" are defined terms.** Transcendence is
  over the specific base `C(w)((t^Gamma))`; the coordinate is
  *differentially* algebraic, satisfying `H' = Omega H` with `Omega` in
  that base, so "transcendental" must not be upgraded to "differentially
  transcendental"; and it is not a claim about any individual value lying
  outside `No[i]`. "Analytic" in the Hamiltonian chapter means exactly the
  entire-coefficient Taylor-compatible realization.
- **Uniqueness is gauge-relative** in the Hamiltonian normal form, and
  resonant normal forms are not claimed unique anywhere.
- **The computations prove nothing infinite.** See below.

Section 21 records the eight open questions in the categories in which they
are open, and Appendix G is a per-theorem hypothesis audit.

## The verification programs

`code/` holds the six programs unmodified and `data/` their recorded
outputs. Totals: **54** (01), **1,109** (02), **21** (03), **2,764** (04),
**245** (05), **119** (06). All six were re-run and all pass. Section 20.1
tabulates exactly what each one checks and each one's own scope
disclaimer — every suite prints one, which is a real and unusual
discipline in this material.

**Run every suite on a copy, never in this tree.** Three of the six scripts
rewrite their own evidence: source 03's writes
`data/verification.json`; source 04's writes `data/verification.json`
*and* `data/coefficients.csv`; source 06's writes
`data/verification.json`. Source 01's script prints to stdout, but its
Makefile's `verify` target redirects that stdout over the delivered
`verification.txt`. A byte-identity check performed after an in-place run
compares two equally modified copies and passes while proving nothing.

What the checks are **not**: they are finite exact symbolic identities. They
do not prove Hahn summability, well-founded recursion, arbitrary-rank
support finiteness, ordinary analytic domain preservation, any
small-divisor limsup, the exact convergence radii, the universal
quantifiers, the classification theorems, the algebraicity dichotomy, the
centralizer theorems, the slow-time theorem, the Liouville construction, or
novelty. Sources 03 and 06 truncate by **total parameter or label degree**,
which is explicitly *not* a Hahn valuation cutoff in a higher-rank group.
Fifty of source 05's 245 assertions are finite lexicographic illustrations
for `n = 1..50`, an illustration and **not** the all-`n` proof, which is in
the text; and its verifier loses one top coefficient on division by `eps`,
so reciprocal and pullback comparisons are checked only through degree
`N-1`. Source 04's README lists a `SHA256SUMS.txt` that does not exist in
the delivered archive — recorded rather than repaired, since `sources/` and
`code/` are preserved unmodified.

Reproducing a suite requires Python 3.10 or later and, for four of them,
SymPy; the pinned version recorded by the sources is `sympy==1.14.0`.

## How to build

Standalone LaTeX with an internal bibliography. No external `.bib` file, no
graphics, no shell escape, no network access.

```sh
latexmk -pdf -interaction=nonstopmode article.tex
```

A standard TeX Live or MiKTeX installation with the packages named in the
preamble suffices. The recorded build is clean: 0 errors, 0 undefined
references, 0 undefined citations, 0 multiply-defined labels, 0 duplicate
PDF destinations, 0 LaTeX warnings and 0 package warnings, 106 pages. All
451 labels carry the `dyn:` prefix.

## Relation to the rest of the collection

- **Extends** `docs/surcomplex/differential-equations/` — its
  ordinary-domain monodromy example (an infinitesimal residue invisible to
  ordinary monodromy) is the antecedent of the monodromy exponent
  `rho_a`, and is cited at the point where `rho_a` is introduced. What is
  new here is the torsion lemma, the finite-cover obstruction, the
  classification of algebraic leading coordinates and the dichotomy — not
  the invisibility phenomenon itself. That report's cross-category warning
  is adopted verbatim, once, in place of re-deriving the
  coordinate-versus-surreal-derivation distinction six times.
- **Inherits from** `docs/surcomplex/analysis/` — the
  no-topological-convergence discipline and the Neumann support material.
  Cited, not restated; five of the six statements of the support lemma are
  deleted.
- **Inherits from** `docs/surcomplex/analytic-geometry/` — the four-ring
  table and its separating witness, neither of which is reprinted. Every
  theorem names its ring in that report's vocabulary, and exactly two rows
  are added (entire coefficients, polynomial coefficients) with the note
  that they are new **rows**, not new rings.
- **Adjacent to** `docs/surcomplex/contours-and-stokes/` — background for
  the period section, and deliberately unused there: every integral is an
  ordinary complex line integral taken coefficient by coefficient over
  ordinary curves in a fixed domain in `C`. A period here is **not** a
  surcomplex contour integral and **not** a residue at a surcomplex point.
- **Kept separate from** `docs/surcomplex/rank-one-berkovich/`, with an
  explicit cross-note (§19.5). That is the one report in the
  collection where convergence is genuine convergence, inside a fixed
  rank-one workspace. This report works at arbitrary rank with a
  deliberately rank-2 example. A Lindahl-type ultrametric disk radius and
  the maximal centered valuation ball here are **different categories**,
  and the exact-ball and shell-periodicity conclusions must not be
  transported to `C_p`. Without that note a reader will read the two
  reports' "disks" as the same object.
