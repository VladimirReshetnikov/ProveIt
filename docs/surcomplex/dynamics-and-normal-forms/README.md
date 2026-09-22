# Surcomplex Dynamics: Linearization Thresholds, Periods, and Normal Forms

**A merged research report.** Everything in this directory other
than `article.tex`, `article.pdf` and this README is preserved source
material.

```
article.tex   the merged report, standalone LaTeX with an internal bibliography
article.pdf   the compiled report
README.md     this guide
code/         the seven source verification programs, unmodified
data/         the seven recorded verification and build records, unmodified
```

## What the report is

Seven independently written manuscripts, all dated 21 September 2026,
developed local and global dynamics over complex Hahn fields
`K = C((t^Gamma))` realized inside `No[i]`, with `Gamma` a set-sized
ordered abelian group of **arbitrary valuation rank**. Sources 01–06 were
written against the pinned repository snapshot
`39f2be6667ade51bca2b45daa47e289d69c09764` and source 07 against
`aa846271b4dcae2c055b216126a87210292ec19b`. This report is their **union**,
not a selection from them.

They share one body of machinery — the set-sized workspace, strong
summability by well-ordered support plus local finiteness, Neumann's
positive-support lemma in finite-word form, halo evaluation by
coefficientwise double Taylor sums, Taylor substitution and its
near-identity inverse — and each of the seven states that machinery from
scratch. Between 45 and 55 per cent of the combined text of sources 01–06
was the same theory, and source 07 restates the same foundation again. The
support lemma appears in all seven.

**Two halves, not seven treatments of one thing.** Sources 01–06 are
germ and fixed-point dynamics — multipliers, return iterates, periods, a
Hamiltonian at the origin of a phase halo — and were merged first. Source
07 is the **quasi-periodic** half: a cohomological equation on a real
torus whose frequency vector has *surreal* components, with divisors
`k . Upsilon` indexed by an integer lattice. It was integrated afterwards
as §§16–18. It is genuinely additive: grepping sources 01–06 for a
resonance lattice, a cohomological equation, a Fourier divisor or a
mean-zero conjugacy to a constant vector field returns nothing, and
conversely source 07 contains no multiplier, no return iterate and no
period. What the two halves share is the machinery above, stated once for
both, and the coefficient-category architecture of Remark 2.2, which is
stated once and **instantiated exactly twice** (Remark 17.2).

## Read Section 2 first: the notion table

Five **inequivalent** conditions travelled under the single word
*resonance* across these seven manuscripts, and six under the words *small
divisor*; worse, two groups of sources used the word *radius* with
**opposite monotonicity**. Unifying the notation without separating the
notions would have produced statements that read correctly and are false.
Section 2 therefore gives each variant its own name and symbol, and every
threshold statement in the report names which variant its hypothesis uses
and in which coefficient category it holds. Section 2.5 is a
theorem-by-theorem tag ledger.

**The five resonances.**

| Tag | Condition | Whose hypothesis it is |
|---|---|---|
| `RES_q` residue-resonant | `lambda` is **never** a root of unity, but its residue has exact finite order `q` | the exact finite-return ball, shell cycles, phase diagram, coherent lifting |
| `MR` / `NR` multiplier-resonant | `lambda^alpha = lambda_j` for some `|alpha| >= 2` | the five-row classification and everything built on the homological operator |
| `FR` frequency-resonant | `omega . k = 0` for some nonzero integer vector | the Hamiltonian package |
| `PAR` parabolic | leading multiplier exactly `1`, perturbed infinitesimally | the algebraicity/monodromy and the period/moduli sections — **with no divisor hypothesis anywhere** |
| `QR` lattice-resonant | `k . Upsilon = 0` for some nonzero integer `k`, where `Upsilon` is a vector of **Hahn (surreal)** scalars | the flag and the linear theorem *permit* it; the torus normal form requires its negation |

`QR` is **not** `FR`. `FR` is a condition on ordinary complex
`omega` in `C^d`, with divisors graded by Taylor degree and all of Hahn
valuation zero; `QR` concerns surreal components, with divisors
`k . Upsilon` graded by the Fourier index `|k|` and of **nonzero**
valuation — which is exactly what Theorem 16.5 is about. Warning 2.9
states the separation and Warning 2.10 adds that the finitely many visible
divisor valuations are **not** a spectrum in any sense this collection
uses.

**The six small-divisor notions.** `SD_0` (support only, no arithmetic
condition at all); `SD_dr` (the rate `sigma`, **requiring multiplier
drift**); `SD_ex` (the rate `tau`, multiplier **exact**); `SD_fr` (the
frequency growth `Theta`); `SD_none` (no condition, and no divisor family
to impose one on); and `SD_ss` (the **stratified subexponential**
condition of source 07: on each stratum of the resonance flag, the
reciprocals of the finitely many **leading real forms** grow
subexponentially in `|k|`).

Remark 2.2 shows that `sigma`, `tau`, `log Theta` and `SD_ss` are one
quantity evaluated on four different divisor families. `SD_ss` is the
*vanishing*-rate condition, so it corresponds to `tau = 0` and
`sigma = 0`, **not** to `tau < infinity` — and it says nothing whatever
about the surreal size `v(k . Upsilon)` of the divisor itself (Warning
2.11).

**The two radii.** Valuation balls `B_r = {v(z) > r}` and valuation
polydisks `D_rho` **shrink** as the threshold grows; ordinary disks and
polydisks `D_R` **grow** as `R` grows. Section 2.4 tabulates both, and the
report distinguishes exponent inequalities from ordinary coefficient estimates.
Passing from valuation exponents to Conway growth exponents negates the
exponent and reverses its threshold inequality; ordinary estimates are unchanged.

## Which archive contributed what

| Source manuscript | Contribution that survives here |
|---|---|
| `01-exact-resonant-return-threshold` | The exact maximal centered valuation ball read off the **finite `q`-th return iterate** rather than off `f` (§8), with the tuned cubic whose factorization `z^5(z^2-2z+2)(z^2-z+2)` moves the threshold from `delta/2` to `delta/4`; the resonant shell theorem with `P(alpha X) = P(X)`, the cycle count and `res(((f^oq)'(p_a)-1)/c) = a P'(a)`; the two-parameter phase diagram `r = max{(delta-sigma)/2, delta/4}` with its three shell polynomials and three leading coordinates (§12); the rank>1 witness that coefficient-valuation bounds are insufficient; the explicit rank-2 `Gamma = Q + Q*Omega` example; the strongly-Hahn-evaluable-but-not-coherent proposition; the return-face stability certificate |
| `02-radius-collapse-trichotomy` | The exact radius law `rad(h_{k,1}) = R exp(-(k+1) sigma)` (§7) and the highest-reciprocal-pole non-cancellation estimate that produces the factor `k+1`; the `Gamma_* = Q + sqrt2 Q` two-independent-exponent design and the explicit refusal to replace `v` by a power of `u`; the trichotomy `CD iff sigma=0`, `CG iff sigma<infinity`, which settles source 03's open question **in the drifted category**; the multiplicative-detuning several-variable version; the critical-scale representability test |
| `03-sharp-small-divisor-thresholds` | **Base of the merge.** The five-row coefficient-category table with per-row necessity witnessed at a single exponent `t^eta` (§6); `tau` and `tau = limsup (log q_{k+1})/q_k` with an explicit non-Brjuno `tau = 0` rotation; exp/log on `G_+(U)` for arbitrary open `U` with no shrinking; the flow law, admissible Hahn times and unique `n`-th roots; fixed-point ideals and their iteration invariance; the centralizer; the finite-order resonant splitting by cyclic averaging; the word-depth radius and degree certificates; workspace invariance with the recorded exception that the centralizer can grow; the two open questions |
| `04-algebraicity-dichotomy-and-monodromy` | The base field `B = C(w)((t^Gamma))` with **arbitrary rational-function** coefficients, not `K(w)`, and the algebraicity dichotomy (algebraic iff `deg V = 1`); the exact `rho_a = Log(1+mu eps)/Log(1+V'(a) eps)` obtained from `A'(a) = Log F'(a)` rather than from a truncated vector field; the torsion lemma and the resulting finite-cover obstruction; the classification of algebraic `h_0` together with the fact that `h_1` is then already transcendental; the sharp disk `v(z) > delta/q` with its **two distinct** failure mechanisms; the all-orders factorization `w(1+w^q)^{rho_q}` |
| `05-common-domain-period-moduli` | The ordinary coefficientwise period of `Omega_F = dz/W_F` as a **complete** conjugacy invariant on a stratum, with a unique basepoint-fixing conjugator; the explicit moduli space, periods giving a bijection onto `m_K^r` on an `r`-punctured plane; the exact five-term difference sequence with cokernel `K^r` and its explicit right inverse; the implicit displacement lemma (where the nowhere-zero hypothesis does its work); the flat/invisible-moduli theorem for `J_delta` nonzero with its `Gamma = Q + Q*omega` instance; the slow-time common-chart lifting theorem; the exact iterative residue `(p+1)/2` |
| `07-small-divisor-resonance-flag` | **The whole quasi-periodic half (§§16–18).** The headline: a frequency vector with `d` surreal components has **at most `d`** arithmetically visible divisor valuations, identified by a canonical descending flag of saturated integer resonance lattices whose ranks strictly drop, together with one explicitly constructed well-ordered set `T_Upsilon` containing the support of *every* reciprocal nonzero divisor (Theorem 16.5); the exact arithmetic criterion `SD_ss`, necessary **and** sufficient for universal solvability of the cohomological equation in a Hahn algebra all of whose coefficients are holomorphic on **one fixed** torus strip (Theorem 17.3), with the valuation loss `kappa_Upsilon` shown attained; the arbitrary-order lifting obstruction — for every `N` an entire forcing whose first `N+1` solution coefficients are analytic while the next is not even a distribution, with robustness under enlarging the value group *argued* from uniqueness of the modewise Hahn inverse rather than assumed (Theorem 17.7); the unique normalized infinitesimal mean-zero conjugacy to a constant vector field with a frequency correction, proved by **marked support words** and exact coefficient stabilization rather than by sequential valuation convergence (Theorem 18.1); necessity of the arithmetic condition even for arbitrarily high-valuation perturbations (Theorem 18.4) and a boundary example at valuation exactly `kappa_Upsilon` with an everywhere-positive slow speed (Proposition 18.6); and the canonical invariant density with its uniqueness (Theorem 18.8). Plus the arithmetic-free valuation bound (Proposition 16.9), which needs no divisor estimate of any kind |
| `06-hahn-normal-form-thresholds` | The entire Hamiltonian chapter (§15): the gauge-normalized symplectic normal form on the whole finite phase space with **no arithmetic bound**; `Theta(omega)` and the sharp homological criterion; commuting actions, and every coherent first integral an entire-coefficient function of them; the coefficientwise holomorphic flow for ordinary complex time; the super-Liouville entire obstruction; the monomial support-and-degree certificate reaching valuation polydisks of **infinite** radius, with separate failure examples for positivity, well-ordering and finite fibers, and the sharp cubic boundary; the multiscale worked example |

## What was deduplicated, and what was kept twice

Printed **once**: the positive-support lemma (all seven state it; sources
02, 03 and 05 each proved the underlying word order by the same
minimal-bad-sequence argument, and one copy is in Appendix A — source 07
needs the *full* finiteness assertion across word lengths, plus a
**labelled** refinement of it counting marked letters, and both are already
contained in that one statement); strong summability; the
`t^gamma = omega^{-gamma}` workspace embedding; halo evaluation; the
coefficient-ring taxonomy; the external-derivative warning; the
fixed-domain-versus-separate-germs distinction, which source 07 instantiates
for its torus strip rather than re-erecting; the coefficient-category table
of Remark 2.2, stated once and instantiated twice with the divisor family
named each time (`lambda^alpha - lambda_j` or `lambda^q - 1` for the germ
half, `k . Upsilon` for the quasi-periodic half); the one-variable
centralizer
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
  of `V` is not available under `RES_q`;
- both instantiations of the coefficient-category table, since only its
  first row ("one fixed unchanged domain, rate zero") is proved on both
  divisor families. Remark 17.2 sets out which rows are **not**
  instantiated on the quasi-periodic side — no polynomial, formal,
  radius-free or entire row is established there, and none is claimed —
  because reading an uninstantiated row across would assert a theorem no
  source proves;
- both Taylor-substitution calculi: the germ half's group law on an open
  `U` in `C^d` is not reproved for the torus, but source 07's Lipschitz
  estimate `v(S_h f - S_g f) >= v(f) + v(h - g)` is genuinely new to the
  report and is what forces uniqueness of the torus normal form.

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

## Correction to finite ancestry

The merged article previously claimed that an operator adding positive
support words could reach a fixed output exponent `gamma` in at most
`ell_S(gamma)` steps, independently of its Hahn input. That is false for
arbitrary input supports: with `T(A) = t A`, the input `t^(-n)` contributes
`T^n(t^(-n)) = 1` at exponent zero after `n` steps, while `ell_{ {1} }(0) = 0`.

Corollary `dyn:cor:ancestry` now keeps the input support `B`. It counts
pairs `(b, w)` with `b in B` and positive word `w` of weight `gamma - b`,
and bounds the number of operator applications by their maximum word
length `ell_{B,S}(gamma)`. The proof counts the finitely many ways to split
a contributing word into nonempty operator steps. It also establishes the
joint summability statement for a strongly summable family of inputs.

The arbitrary-input substitution, exponential/logarithm, discrete-equation
and torus-substitution proofs now retain this dependence explicitly.
The linearizer's stronger bound `k + 1 <= ell_S(gamma)` is unchanged:
its initial input `L^(-1) f` already supplies a positive letter from `S`.
The associated radius and degree bounds therefore keep their stated form.

Source 03, retained in Git history, already distinguished arbitrary input support in
its lemma “Adding an arbitrary input support” and claimed only finite
dependence in “Support-increasing operators.” The incorrect absolute bound
was introduced in the merged corollary. The original manuscripts are now
accessible through Git history; the verification programs and recorded
outputs in `code/` and `data/` remain unchanged. The corrected combinatorial statement
and counterexample are checked in
[`Ancestry.lean`](../../../Surreal/HahnSeries/Ancestry.lean); the full
operator statement has a mathematical proof here but is not yet formalized.
See the [formalization ledger](../../FORMALIZATION.md) for exact coverage.

## What is NOT claimed

Section 25 is the consolidated record: **80 numbered items covering the 78
distinct limitations stated by the seven sources**, distributed
11/9/10/14/12/12/10 across sources 01–07, each with its originating source
named. None was merged away or softened. The load-bearing ones:

- **Status.** Seven AI-assisted, unrefereed research drafts; the full merged
  report is not proof-assistant verified. The repository now has checked
  Lean proofs of the finite-word support lemma, the corrected combinatorial
  ancestry bounds, and the counterexample above. This partial coverage
  does not certify the operator calculus or the analytic classification
  theorems. Priority is not certified for any statement and no named published
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
- **No uniform coefficient norm bound.** No uniform ordinary norm bound on any
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
  critical-scale obstructions are collected in §20 precisely so they
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
- **The quasi-periodic half is a coefficientwise Hahn theory.** It does
  **not** assert convergence after substituting a nonzero real parameter
  for a Hahn monomial, and **does not improve classical real analytic KAM
  or Brjuno arithmetic**: a series lies in the fixed-strip algebra
  however fast its coefficient seminorms grow. Its torus derivatives are
  **external** derivations annihilating the Hahn scalar field, not the
  Berarducci–Mantova derivation, so nothing there speaks to internal
  surreal differential equations. **A common support is not
  summability**: the family of reciprocal divisors indexed by the Fourier
  modes is in general *not* Hahn-summable, and only a common support is
  proved. The invariant density is coefficientwise integration, **not** a
  countably additive `No`-valued measure and **not** an ergodic theorem.
  The nonlinear theorem needs a trivial exact resonance lattice, and the
  source warns that replacing the mean projection by the resonant one is
  *not* justified. The flag is finite but **not automatically
  computable**: existence is separated from decidability of its
  entries.
- **The computations prove nothing infinite.** See below.

Section 24 records the eleven open questions in the categories in which
they are open, and Appendix G is a per-theorem hypothesis audit.

## The verification programs

`code/` holds the seven programs unmodified and `data/` their recorded
outputs. Totals where a script prints one: **54** (01), **1,109** (02),
**21** (03), **2,764** (04), **245** (05), **119** (06); source 07 prints
no total but checks the slow-circle conjugacy through degree ten, **117**
exact coefficient recurrences, and the stratum classification of **1,330**
integer modes into **1,210 / 110 / 10**. All seven were re-run and all
pass. Section 23.1 tabulates exactly what each one checks and each one's
own scope disclaimer — every suite prints one, which is a real and unusual
discipline in this material.

**Run every suite on a copy, never in this tree.** Four of the seven
scripts rewrite their own evidence: source 03's writes
`data/verification.json`; source 04's writes `data/verification.json`
*and* `data/coefficients.csv`; source 06's writes
`data/verification.json`; and source 07's takes `--output` with **default**
`verification.json` resolved against the current working directory, written
with an unconditional `write_text` — no existence check, no backup, no dry
run — so the invocation documented in its own README is exactly the one
that overwrites the delivered record. Source 01's script prints to stdout,
but its Makefile's `verify` target redirects that stdout over the delivered
`verification.txt`. A byte-identity check performed after an in-place run
compares two equally modified copies and passes while proving nothing.

**Independently checked, beyond running the suites.** The finiteness bound
of Theorem 16.5 was verified without source 07: writing the divisor as a
sum of real linear forms against the frequency's Hahn coefficients makes
the level sets intersections of kernels, so a new level appears exactly
when the kernel rank strictly drops — at most `d` times. **400 random
trials** over rational coefficient matrices, with resonances deliberately
forced in 40 per cent of them, gave **zero violations**; a worked instance
at `d = 3` had kernel ranks 2 → 1 → 0 with achieved levels `{0, 1, 3}`,
attaining the bound with two indices skipped exactly where the rank did
not move. Section 23.2 records this.

What the checks are **not**: they are finite exact symbolic identities. They
do not prove Hahn summability, well-founded recursion, arbitrary-rank
support finiteness, ordinary analytic domain preservation, any
small-divisor limsup, the exact convergence radii, the universal
quantifiers, the classification theorems, the algebraicity dichotomy, the
centralizer theorems, the slow-time theorem, the Liouville construction, or
novelty. Source 07's checks in particular verify neither the irrationality
of its Liouville constant, nor any infinite-mode subexponential estimate,
nor the word lemma, nor the infinite-support conjugacy theorem. Sources 03
and 06 truncate by **total parameter or label degree**,
which is explicitly *not* a Hahn valuation cutoff in a higher-rank group.
Fifty of source 05's 245 assertions are finite lexicographic illustrations
for `n = 1..50`, an illustration and **not** the all-`n` proof, which is in
the text; and its verifier loses one top coefficient on division by `eps`,
so reciprocal and pullback comparisons are checked only through degree
`N-1`. Sources 04 and 07 both list a `SHA256SUMS.txt` in their READMEs that does
not exist in the delivered archive — recorded rather than repaired.

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
PDF destinations, 0 LaTeX warnings and 0 package warnings, 130 pages. All
540 labels carry the `dyn:` prefix.

## Relation to the rest of the collection

- **Extends** `docs/surcomplex/differential-equations/` — its
  ordinary-domain monodromy example (an infinitesimal residue invisible to
  ordinary monodromy) is the antecedent of the monodromy exponent
  `rho_a`, and is cited at the point where `rho_a` is introduced. What is
  new here is the torsion lemma, the finite-cover obstruction, the
  classification of algebraic leading coordinates and the dichotomy — not
  the invisibility phenomenon itself. That report's cross-category warning
  is adopted verbatim, once, in place of re-deriving the
  coordinate-versus-surreal-derivation distinction seven times. Source 07
  separates itself from that report **by name**: its torus derivatives are
  external derivations annihilating the Hahn scalar field, so the
  cohomological equation of §17 is not a surreal differential equation for
  the Berarducci–Mantova derivation, and no theorem of either report
  transfers to the other. It also records that a targeted repository code
  search for "cohomological" returned no match, while stating that this is
  not an exhaustive audit.
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
  explicit cross-note (§22.5). That is the one report in the
  collection where convergence is genuine convergence, inside a fixed
  rank-one workspace. This report works at arbitrary rank with a
  deliberately rank-2 example. A Lindahl-type ultrametric disk radius and
  the maximal centered valuation ball here are **different categories**,
  and the exact-ball and shell-periodicity conclusions must not be
  transported to `C_p`. Without that note a reader will read the two
  reports' "disks" as the same object.
