# Surcomplex Dynamics: Linearization Thresholds, Periods, and Normal Forms

**A merged research report** built from ten manuscripts: sources 01–07, dated
21 September 2026, and sources 08–10, dated 22 September 2026. Everything in
this directory other than `article.tex`, `article.pdf` and this README is
preserved source material.

```
article.tex   the merged report, standalone LaTeX with an internal bibliography
article.pdf   the compiled report, 171 pages
README.md     this guide
08-exact-and-drifting-multipliers-SOURCE_AUDIT.md
              source 08's own source-and-claim audit, as delivered
09-single-loss-linearization-repository_scope.md
              source 09's own provenance and scope note, as delivered
10-nonscalar-common-domain-SOURCES.md
              source 10's own source and provenance ledger, as delivered
code/         the ten source verification programs, and the build helpers
              of sources 01, 03, 04, 05, 06, 08 and 09, unmodified
data/         the recorded verification, environment and build records of
              the ten sources, unmodified
```

Every label in `article.tex` carries the prefix `dyn:`. Material added from
sources 08 and 09 carries a sub-prefix: `dyn:esm:` (the exact scalar
multiplier, §7), `dyn:tree:` (source 09's forward plane-tree route, §7.4)
and `dyn:cyc:` (the single cyclic exponent, §8.6). Material added from
source 10 carries the sub-prefix `dyn:nsc:` (the nonscalar diagonal
multiplier, §§7.7–7.13, and its non-claims, §26.10). **No existing label was
renamed or removed.** The report had 540 labels before sources 08 and 09
were added, 610 before source 10 was added, and has 651 now; all 610 are
still present. `docs/FORMALIZATION.md` cites existing `dyn:` labels only.
Its statement index records source line numbers, which have moved.

The two shipped notes of sources 08 and 09 describe this report as it stood
at their pin `a3124af`. The labels they cite (`dyn:q:commongerm`,
`dyn:q:commongerm-restate`, `dyn:q:cyclic`, `dyn:thm:main`, `dyn:prop:linearization`, `dyn:prop:halo`,
`dyn:prop:monad`) are unchanged, but the line ranges quoted in
`08-exact-and-drifting-multipliers-SOURCE_AUDIT.md` have moved since then.
Both questions they call open are now partly settled, by these same two
sources (see below). The audit also names its files by their delivered
paths (`code/verify.py`, `data/verification.json`, `data/build_report.json`),
which here are `code/08-exact-and-drifting-multipliers-verify.py`,
`data/08-exact-and-drifting-multipliers-verification.json` and
`data/08-exact-and-drifting-multipliers-build_report.json`. The standalone
source manuscripts and their PDFs are not shipped.

Source 10's shipped `10-nonscalar-common-domain-SOURCES.md` describes this
report at its pin `048b72c`. That commit is later than the merge of sources
08 and 09 (`813ce54`), and at it `article.tex` was byte-identical to the
version just before source 10 was added (blob `a95e062`). So its statement
that the report leaves the nonscalar common-domain case open, and that the
scalar theorem is already here and not claimed, is accurate for that
version; the case is now settled except for the optimal radius (see below).
The labels it cites (`dyn:thm:radius-depth`, `dyn:q:commongerm`,
`dyn:esm:thm:treebound`, `dyn:esm:thm:main`, `dyn:prop:cf`) are unchanged.
It names its files `verify.py` and `verification_results.txt`, which here
are `code/10-nonscalar-common-domain-verify.py` and
`data/10-nonscalar-common-domain-verification_results.txt`. Source 10's
article, PDF, README and checksum manifest are not shipped; the manifest's
six entries were checked against the delivered files before it was dropped.

## What the report is

Ten independently written manuscripts developed local and global dynamics
over complex Hahn fields `K = C((t^Gamma))` realized inside `No[i]`, with
`Gamma` a set-sized ordered abelian group of **arbitrary valuation rank**.
Sources 01–06 were written against the pinned repository snapshot
`39f2be6667ade51bca2b45daa47e289d69c09764`, source 07 against
`aa846271b4dcae2c055b216126a87210292ec19b`, sources 08 and 09 against
`a3124af79f66b8b9c196d76b4cbc5ac3938907c4`, and source 10 against
`048b72cf7cbfc8ab246e4f73788c10460cb3f6e0`. This report is their **union**,
not a selection from them.

They share one body of machinery: the set-sized workspace; strong
summability by well-ordered support plus local finiteness; Neumann's
positive-support lemma in finite-word form; halo evaluation by
coefficientwise double Taylor sums; and Taylor substitution with its
near-identity inverse. Each of the ten states that machinery from scratch.
Between 45 and 55 per cent of the combined text of sources 01–06 was the
same theory, and sources 07–10 restate the same foundation again.
The support lemma appears in all ten.

**Two halves, not ten treatments of one thing.** Sources 01–06 are
germ and fixed-point dynamics — multipliers, return iterates, periods, a
Hamiltonian at the origin of a phase halo — and were merged first. Source
07 is the **quasi-periodic** half: a cohomological equation on a real
torus whose frequency vector has *surreal* components, with divisors
`k . Upsilon` indexed by an integer lattice. It was integrated afterwards
as §§17–19. It is genuinely additive: grepping sources 01–06 for a
resonance lattice, a cohomological equation, a Fourier divisor or a
mean-zero conjugacy to a constant vector field returns nothing, and
conversely source 07 contains no multiplier, no return iterate and no
period. What the two halves share is the machinery above, stated once for
both, and the coefficient-category architecture of Remark 2.2. That
architecture is stated once and **instantiated exactly twice** (Remark 18.2).

Sources 08 and 09 belong to the germ half and were integrated last, as §7
and §8.6. Both answer, for a scalar multiplier, the question the report had
left open for an **exact** multiplier (Question 8.20, restated as Question 25.1), and source 08 also
answers the fixed-cyclic-group question (Question 25.2). They prove the same
sharp radius by different routes and contradict neither each other nor any
earlier source; see "The one conflict" below.

Source 10 also belongs to the germ half and was integrated after them, as
§§7.7–7.13, at the end of §7. It answers the case that sources 08 and 09
left open, a **nonscalar** exact diagonal unitary multiplier: every
coefficient of the normalized conjugacy and its inverse is holomorphic on
one polydisk of radius `R exp(-r_ang tau)`, where `r_ang` is the rational
rank of the multiplier's angles (Theorem 7.23). This is sharp when
`r_ang = 1`, which includes every scalar multiplier and many nonscalar ones;
for `r_ang >= 2` only the optimal radius is left open (Theorem 7.34,
Question 25.1). Source 10 read this report after sources 08 and 09 were
merged and cites their scalar theorem rather than claiming it.

## Read Section 2 first: the notion table

Five **inequivalent** conditions travelled under the single word
*resonance* across these manuscripts, and six under the words *small
divisor*. Worse, two groups of sources used the word *radius* with
**opposite monotonicity**. Unifying the notation without separating the
notions would have produced statements that read correctly and are false.
Section 2 therefore gives each variant its own name and symbol. Every
threshold statement in the report names which variant its hypothesis uses
and in which coefficient category it holds. Section 2.5 is a
theorem-by-theorem tag ledger. Sources 08, 09 and 10 introduce no new
notion; their statements are tagged `NR`, `SD_ex` (§7) and `SD_dr` (§8.6).
Source 10 adds an arithmetic invariant of an exact multiplier, the rational
angular rank `r_ang = dim_Q span_Q(1, theta_1, ..., theta_d) - 1`. It is
written `r_ang`, not source 10's `r`, because `r` already names the
finite-return threshold, an auxiliary radius, a chain length and the flag
length; and it is **not** the valuation rank of `Gamma`.

**The five resonances.**

| Tag | Condition | Whose hypothesis it is |
|---|---|---|
| `RES_q` residue-resonant | `lambda` is **never** a root of unity, but its residue has exact finite order `q` | the exact finite-return ball, shell cycles, phase diagram, coherent lifting |
| `MR` / `NR` multiplier-resonant | `lambda^alpha = lambda_j` for some `|alpha| >= 2` | the five-row classification, the exact-scalar and cyclic theorems of sources 08–09, the nonscalar theorem of source 10, and everything built on the homological operator |
| `FR` frequency-resonant | `omega . k = 0` for some nonzero integer vector | the Hamiltonian package |
| `PAR` parabolic | leading multiplier exactly `1`, perturbed infinitesimally | the algebraicity/monodromy and the period/moduli sections — **with no divisor hypothesis anywhere** |
| `QR` lattice-resonant | `k . Upsilon = 0` for some nonzero integer `k`, where `Upsilon` is a vector of **Hahn (surreal)** scalars | the flag and the linear theorem *permit* it; the torus normal form requires its negation |

`QR` is **not** `FR`. `FR` is a condition on ordinary complex
`omega` in `C^d`, with divisors graded by Taylor degree and all of Hahn
valuation zero. `QR` concerns surreal components, with divisors
`k . Upsilon` graded by the Fourier index `|k|` and of **nonzero**
valuation, which is exactly what Theorem 17.5 is about. Warning 2.9
states the separation. Warning 2.10 adds that the finitely many visible
divisor valuations are **not** a spectrum in any sense this collection
uses.

**The six small-divisor notions.** `SD_0` (support only, no arithmetic
condition at all); `SD_dr` (the rate `sigma`, **requiring multiplier
drift**; sources 02 and 08); `SD_ex` (the rate `tau`, multiplier **exact**;
sources 03, 08, 09 and 10); `SD_fr` (the frequency growth `Theta`); `SD_none`
(no condition, and no divisor family to impose one on); and `SD_ss` (the
**stratified subexponential** condition of source 07: on each stratum of
the resonance flag, the reciprocals of the finitely many **leading real
forms** grow subexponentially in `|k|`).

Remark 2.2 shows that `sigma`, `tau`, `log Theta` and `SD_ss` are one
quantity evaluated on four different divisor families. `SD_ss` is the
*vanishing*-rate condition, so it corresponds to `tau = 0` and
`sigma = 0`, **not** to `tau < infinity`. It says nothing whatever about the
surreal size `v(k . Upsilon)` of the divisor itself (Warning 2.11).
Remark 2.2 now also records the **sixth category**, common-domain germs,
in two separate cells that must never be merged: for an exact scalar
multiplier it holds iff `tau < infinity` (sources 08, 09); under drift it
holds iff `sigma = 0` (sources 02, 08). For an exact nonscalar diagonal
multiplier it also holds iff `tau < infinity`, with universal radius between
`R exp(-r_ang tau)` and `R exp(-tau)`, equal to the latter when `r_ang = 1`
(source 10); the optimal radius for `r_ang >= 2` is open.

**The two radii.** Valuation balls `B_r = {v(z) > r}` and valuation
polydisks `D_rho` **shrink** as the threshold grows; ordinary disks and
polydisks `D_R` **grow** as `R` grows. Section 2.4 tabulates both, and the
report distinguishes exponent inequalities from ordinary coefficient estimates.
Passing from valuation exponents to Conway growth exponents negates the
exponent and reverses its threshold inequality; ordinary estimates are unchanged.

## Which archive contributed what

| Source manuscript | Contribution that survives here |
|---|---|
| `01-exact-resonant-return-threshold` | The exact maximal centered valuation ball read off the **finite `q`-th return iterate** rather than off `f` (§9), with the tuned cubic whose factorization `z^5(z^2-2z+2)(z^2-z+2)` moves the threshold from `delta/2` to `delta/4`; the resonant shell theorem with `P(alpha X) = P(X)`, the cycle count and `res(((f^oq)'(p_a)-1)/c) = a P'(a)`; the two-parameter phase diagram `r = max{(delta-sigma)/2, delta/4}` with its three shell polynomials and three leading coordinates (§13); the rank>1 witness that coefficient-valuation bounds are insufficient; the explicit rank-2 `Gamma = Q + Q*Omega` example; the strongly-Hahn-evaluable-but-not-coherent proposition; the return-face stability certificate |
| `02-radius-collapse-trichotomy` | The exact radius law `rad(h_{k,1}) = R exp(-(k+1) sigma)` (§8) and the highest-reciprocal-pole non-cancellation estimate that produces the factor `k+1`; the `Gamma_* = Q + sqrt2 Q` two-independent-exponent design and the explicit refusal to replace `v` by a power of `u`; the trichotomy `CD iff sigma=0`, `CG iff sigma<infinity`, which settles source 03's open question **in the drifted category**; the multiplicative-detuning several-variable version; the critical-scale representability test |
| `03-sharp-small-divisor-thresholds` | **Base of the first merge.** The five-row coefficient-category table with per-row necessity witnessed at a single exponent `t^eta` (§6); `tau` and `tau = limsup (log q_{k+1})/q_k` with an explicit non-Brjuno `tau = 0` rotation; exp/log on `G_+(U)` for arbitrary open `U` with no shrinking; the flow law, admissible Hahn times and unique `n`-th roots; fixed-point ideals and their iteration invariance; the centralizer; the finite-order resonant splitting by cyclic averaging; the word-depth radius and degree certificates; workspace invariance with the recorded exception that the centralizer can grow; the two open questions |
| `04-algebraicity-dichotomy-and-monodromy` | The base field `B = C(w)((t^Gamma))` with **arbitrary rational-function** coefficients, not `K(w)`, and the algebraicity dichotomy (algebraic iff `deg V = 1`); the exact `rho_a = Log(1+mu eps)/Log(1+V'(a) eps)` obtained from `A'(a) = Log F'(a)` rather than from a truncated vector field; the torsion lemma and the resulting finite-cover obstruction; the classification of algebraic `h_0` together with the fact that `h_1` is then already transcendental; the sharp disk `v(z) > delta/q` with its **two distinct** failure mechanisms; the all-orders factorization `w(1+w^q)^{rho_q}` |
| `05-common-domain-period-moduli` | The ordinary coefficientwise period of `Omega_F = dz/W_F` as a **complete** conjugacy invariant on a stratum, with a unique basepoint-fixing conjugator; the explicit moduli space, periods giving a bijection onto `m_K^r` on an `r`-punctured plane; the exact five-term difference sequence with cokernel `K^r` and its explicit right inverse; the implicit displacement lemma (where the nowhere-zero hypothesis does its work); the flat/invisible-moduli theorem for `J_delta` nonzero with its `Gamma = Q + Q*omega` instance; the slow-time common-chart lifting theorem; the exact iterative residue `(p+1)/2` |
| `06-hahn-normal-form-thresholds` | The entire Hamiltonian chapter (§16): the gauge-normalized symplectic normal form on the whole finite phase space with **no arithmetic bound**; `Theta(omega)` and the sharp homological criterion; commuting actions, and every coherent first integral an entire-coefficient function of them; the coefficientwise holomorphic flow for ordinary complex time; the super-Liouville entire obstruction; the monomial support-and-degree certificate reaching valuation polydisks of **infinite** radius, with separate failure examples for positivity, well-ordering and finite fibers, and the sharp cubic boundary; the multiscale worked example |
| `07-small-divisor-resonance-flag` | **The whole quasi-periodic half (§§17–19).** The headline: a frequency vector with `d` surreal components has **at most `d`** arithmetically visible divisor valuations, identified by a canonical descending flag of saturated integer resonance lattices whose ranks strictly drop, together with one explicitly constructed well-ordered set `T_Upsilon` containing the support of *every* reciprocal nonzero divisor (Theorem 17.5); the exact arithmetic criterion `SD_ss`, necessary **and** sufficient for universal solvability of the cohomological equation in a Hahn algebra all of whose coefficients are holomorphic on **one fixed** torus strip (Theorem 18.3), with the valuation loss `kappa_Upsilon` shown attained; the arbitrary-order lifting obstruction — for every `N` an entire forcing whose first `N+1` solution coefficients are analytic while the next is not even a distribution, with robustness under enlarging the value group *argued* from uniqueness of the modewise Hahn inverse rather than assumed (Theorem 18.7); the unique normalized infinitesimal mean-zero conjugacy to a constant vector field with a frequency correction, proved by **marked support words** and exact coefficient stabilization rather than by sequential valuation convergence (Theorem 19.1); necessity of the arithmetic condition even for arbitrarily high-valuation perturbations (Theorem 19.4) and a boundary example at valuation exactly `kappa_Upsilon` with an everywhere-positive slow speed (Proposition 19.6); and the canonical invariant density with its uniqueness (Theorem 19.8). Plus the arithmetic-free valuation bound (Proposition 17.9), which needs no divisor estimate of any kind |
| `08-exact-and-drifting-multipliers` | **Base of the 08+09 merge** (weaker hypotheses: every dimension `d`; it also carries the drifted theorem). *Exact and Drifting Multipliers in Surcomplex Dynamics*. The sharp common domain for an exact **scalar** multiplier `lambda I_d` in every dimension: all coefficients of the normalized conjugacy and its inverse are holomorphic on the one polydisk of radius `R exp(-tau)`, which is optimal (Theorem 7.13, with the strict degree chains of Lemma 7.9 and the depth-uniform estimate of Proposition 7.11); the unequal-radius rescaling `R_j exp(-tau)`; the sixth-category row (Corollary 7.14); the **single-cyclic-exponent collapse** over `Z`: for `(lambda+t)z + t z^2/(1-z/R)` the coefficient of `t^m` has radius exactly `R exp(-m sigma)` (Theorem 8.15), by the collision noncancellation at convergent denominators (Proposition 8.14) and the pole-multiplicity lemma (Lemma 8.11); the fixed-group criterion `CD iff sigma=0` over any fixed nonzero `Gamma` (Corollary 8.17); one positive Hahn coefficient suffices (Corollary 8.18); the `tau = log 2` comparison `R/2` against `R/2^m` (Example 8.19); the nonscalar-boundary analysis (§7.6); the SymPy suite with the cyclic fold test; `SOURCE_AUDIT.md` |
| `09-single-loss-linearization` | *A Single-Loss Theorem for Exact-Multiplier Surcomplex Linearization*, one variable. The **tree product bound** `prod 1/|lambda^{s_v}-1| <= (C_a n)^m e^{a n}` for positively weighted forests, with the cluster threshold `1/(4n)` (Theorem 7.5). Source 08's strict-chain bound, whose polynomial factor is `n^{3r}`, becomes the chain case of this bound (Corollary 7.6(i)) and is credited there; the forward plane-tree route, **kept as route D** (§7.4: Proposition 7.17, Lemma 7.18, Proposition 7.19), which is a second proof of Theorem 7.13 for `d = 1`; several formal parameters (Corollary 7.20); the lex `Z^2` example (Example 7.21); the hypothesis-use audit (Table 5); its limitations; `repository_scope.md` |
| `10-nonscalar-common-domain` | *Common-Domain Linearization over Surcomplex Hahn Fields: a rational-rank bound for nonscalar multipliers* (§§7.7–7.13, §26.10). The nonscalar common domain: for an exact diagonal unitary nonresonant `Lambda` with `tau < infinity`, all coefficients of the normalized conjugacy and its inverse are holomorphic on the polydisk of radius `R exp(-r_ang tau)`, over every nonzero `Gamma`, whatever the support (Theorem 7.23); the integer-minor lemma that at most `q` distinct positive exponential rates occur for a linear form in `q` variables along linearly growing integer vectors (Lemma 7.24, Corollary 7.25); marked-block contraction of colored trees, which keeps each block's divisor inside the nonlinear cone (Lemma 7.26); the product bound `limsup n^{-1} log A^Lambda_m(n) <= min(r_ang, m) tau` at fixed complexity (Theorem 7.27), with equality `tau` in rank one (Corollary 7.28); route D in several variables by colored trees, with a polynomial diagram count that has no factor `d^{n+1}` (Proposition 7.30, Lemma 7.31); the input-relative radius `R_gamma exp(-min(r_ang, ell_S(gamma)) tau)`, which improves Theorem 6.9 (Corollary 7.32); rectangular polydisks and joint holomorphy in ordinary parameters (Corollary 7.33); the exact criterion `tau < infinity` and `R exp(-r_ang tau) <= R_univ <= R exp(-tau)`, sharp for `r_ang = 1` (Theorem 7.34); the two-mode example `diag(lambda^2, lambda^3)` with `tau = 3 tau(lambda)` and any prescribed loss factor (Proposition 7.35); a rank-two zero-loss example (Example 7.36); the exact standard-library suite; `SOURCES.md` |

Sources 08 and 09 are each written in their own convention, and the merge
had to choose between them. Source 08 uses the report's convention
`H o F = lambda H`. Source 09 uses the **forward** convention
`F o H = H o (lambda .)`, so its `H` is this report's `H^{-1}`, written
`check H` here. Every formula of source 09 was translated; for example its
sharp first coefficient is `check h_eta = -h_eta` (Convention 7.1(iii)).

## What was deduplicated, and what was kept twice

Printed **once**:

- The positive-support lemma. All ten sources state it. Sources 02, 03, 05
  and 09 each prove the underlying word order by the same
  minimal-bad-sequence argument, and one copy is in Appendix A. Source 10
  derives it from Higman's lemma, cited. Source 07
  needs the *full* finiteness assertion across word lengths, plus a
  **labelled** refinement of it counting marked letters, and both are
  already contained in that one statement. Source 08's reduction to
  Poonen's theorem over a free associative algebra is recorded in one
  sentence as a second route (Remark 7.15).
- Strong summability; the `t^gamma = omega^{-gamma}` workspace embedding;
  halo evaluation; the coefficient-ring taxonomy; the external-derivative
  warning.
- The fixed-domain-versus-separate-germs distinction, which source 07
  instantiates for its torus strip rather than re-erecting.
- The coefficient-category table of Remark 2.2, stated once and
  instantiated twice with the divisor family named each time
  (`lambda^alpha - lambda_j` or `lambda^q - 1` for the germ half,
  `k . Upsilon` for the quasi-periodic half).
- The one-variable centralizer. Sources 03 and 05 state it with the same
  hypotheses, the same conclusion, the same meromorphic-ratio proof and the
  same remark that zeros of `a` need not be removed.
- The continued-fraction formula for the divisor rate, together with the
  prescribed-rate and rate-zero non-Brjuno constructions. Sources 08 and
  09 reprove them; source 09's rate-zero example is Theorem 8.9(b) exactly.
- The leading-coefficient exponential integral
  `h_0 = w exp int (mu/V_0 - 1/w)`. Source 01's `H_0` with `V_0 = X P(X)`
  and source 04's with `V_0 = V` are the same formula, proved by the same
  transfinite variation-of-constants recursion.
- The degree-six iterative logarithm of `z + t z^2`, which sources 03 and
  05 each compute.
- The quadratic Schröder recursion. Six sources compute it, in six
  normalizations; it is printed once with the translation between them
  (§22.1; source 09's coefficients are those of the inverse coordinate).
- From sources 08 and 09 together: the one-rational clustering lemma
  (Lemma 7.2; source 08's cutoff `n^{-3}` is the same argument); the
  divisible-subtree packing lemma (Lemma 7.3); the sharp witness, which is
  the report's `P_R` of (5.6) up to a factor `R`; the scalar common-domain
  theorem itself (Theorem 7.13, credited to both); same-domain inversion,
  halo realization, workspace invariance and monad evaluation, which
  duplicate Propositions 4.1, 6.13, 4.14 and 6.14 and are cited; and source
  09's entire-row witness, which is Lemma 5.2.
- From source 10: the first-weight identity (Proposition 6.6); the universal
  upper radius `R exp(-tau)` and the infinite-rate entire witness (Lemma
  5.2; source 10's remark that the finite witness needs no case distinction
  at `tau = 0` is kept in the proof of Theorem 7.34); the positive inverse
  on the same domain (Proposition 4.1); halo realization (Proposition 6.13);
  workspace invariance (Proposition 4.14); the surcomplex embedding and
  monad evaluation; the prescribed-rate continued fraction (Theorem 8.9(c),
  with the formula of Proposition 8.8); the higher-rank support
  `S = {1} u {2 - 1/n} u {Omega}` (Example 3.7); and the lexicographic `Z^2`
  caution (Example 7.21). Source 10's appendix restating Theorem 7.27
  without Hahn fields is the same statement and is not reprinted.

Kept **twice or more, explicitly marked**, because the routes carry
different resources:

- **four** routes to a support-controlled linearizer:
  - an operator geometric series, which yields the word-depth bound and
    hence the radius and degree certificates, and which in §7 yields the
    strict degree chains;
  - an exponent-by-exponent well-founded recursion, which accommodates
    multiplier **drift**;
  - a Taylor-degree recurrence with a pre-cancelled infinitesimal divisor,
    which makes the finite-return threshold exact;
  - source 09's forward plane-tree expansion (route D, §7.4), which uses
    the branching case of the tree bound. Routes A and D share the
    arithmetic lemmas and are **not** independent proofs of them, as source
    09 itself says. Source 09's own operator-chain appendix is route A and
    is not reprinted. Source 10 extends route D to several variables and
    nonscalar `Lambda` with colored trees (§7.10).
- two arguments for the fixed-complexity rate `tau` of a **scalar**
  multiplier: the explicit tree bound `(C_a n)^m e^{a n}` of sources 08 and
  09 (one rational cluster plus divisible-subtree packing), and source 10's
  rate count plus block budget, which gives only a limsup with a
  non-explicit prefactor but is the one that works for nonscalar `Lambda`
  (Remark 7.29). In the scalar case source 10 adds nothing new; the
  explicit bound is strictly more information;
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
  divisor families. Remark 18.2 sets out which rows are **not**
  instantiated on the quasi-periodic side — no polynomial, formal,
  radius-free, entire or common-domain row is established there, and none
  is claimed — because reading an uninstantiated row across would assert a
  theorem no source proves;
- both Taylor-substitution calculi: the germ half's group law on an open
  `U` in `C^d` is not reproved for the torus, but source 07's Lipschitz
  estimate `v(S_h f - S_g f) >= v(f) + v(h - g)` is genuinely new to the
  report and is what forces uniqueness of the torus normal form.

## The one conflict across the sources, and how it is resolved

Source 03 poses as **open** whether the common-domain germ category fails
for an intermediate divisor rate. It proves only a word-depth lower bound and
states explicitly that this does **not** prove radius collapse. Source 02
proves outright **failure**, with the exact law
`rad(h_{k,1}) = R exp(-(k+1) sigma)`.

This is not a contradiction, and each source says so. Source 02's negative
direction **requires** multiplier drift `F'(0) = lambda + u` and two
rationally independent positive exponents, both of which source 03
excludes: its multiplier is *exactly* `Lambda`, with no infinitesimal
linear part at any Hahn exponent. The report therefore prints source 02's
theorem as the answer **in the drifted category**, where it settles the
question negatively. Source 02 itself records that eliminating drift
removes the reciprocal-jet mechanism.

At the pins of sources 01–07 the question stayed **open for the
fixed-multiplier category**. Sources 08 and 09 have since answered it
there for a **scalar** multiplier, and the answer is the opposite one:
every coefficient is holomorphic on one polydisk of the sharp radius
`R exp(-tau)` (Theorem 7.13). Source 08 also removed the second exponent
from the drifted collapse: over `Z`, with one Hahn monomial, the radii are
`R exp(-m sigma)` (Theorem 8.15), and drift is still required. The report
keeps the two answers in separate rows (Remark 2.2, Table 7). The exact
laws are never quoted without their drift hypothesis (Warnings 2.6 and
8.21), and the two categories are not averaged into a single
"intermediate case" claim. For a **nonscalar** exact multiplier the
question was still open at the pins of sources 08 and 09. Source 10 has
since answered it the same way as for a scalar one: every input has a
common-domain linearizer, of radius at least `R exp(-r_ang tau)`, and
exactly `R exp(-tau)` universally when `r_ang = 1` (Theorems 7.23 and
7.34). Only the optimal radius for `r_ang >= 2` is open (Question 25.1).

Sources 08 and 09 do not contradict each other. Source 09 says it settles
only one variable and not the drifted or cyclic questions. Source 08
settles the scalar case in every dimension and the cyclic question in one
variable. Both agree that the nonscalar diagonal case is open, as it was
when they wrote. Source 10 contradicts neither: it cites their scalar
theorem, recovers its constant only in angular rank one, and leaves the
drifted and cyclic questions alone.

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
Sources 08, 09 and 10 use only this linearizer bound, through the initial
letter of the linearizer, so the correction does not affect them.

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

## What the new material claims, precisely

- **Theorem 7.13** (sources 08, 09). Let `lambda = e^{2 pi i theta}`, with
  `theta` irrational, and `tau = limsup n^{-1} log^+ |lambda^n - 1|^{-1}`.
  Take any nonzero set-sized `Gamma`, any `d >= 1`, and an exact input
  `lambda z + sum_s t^s f_s` whose coefficients `f_s` are holomorphic on one
  polydisk of radius `R` and satisfy `f_s(0) = 0` and `Df_s(0) = 0`. If
  `tau` is finite, the normalized conjugacy and its inverse have **all**
  coefficients holomorphic on the open polydisk of radius `R exp(-tau)`.
  That radius is the optimal universal one, attained at the first Hahn
  coefficient of `lambda z + t^eta P_R(z_1) e_1`. If `tau` is infinite, the
  same input has a first coefficient of radius zero.
- **Theorem 7.5** (source 09). For positively weighted forests with `m`
  vertices and total weight `n`, the product of the inverse divisors at the
  subtree weights is at most `(C_a n)^m e^{a n}`. So the rate at fixed
  complexity is `tau`, not `m tau` (Corollary 7.6).
- **Theorem 8.15** (source 08; **drift required**). Over `C((t))`, value
  group `Z`, the map `(lambda + t) z + t z^2/(1 - z/R)` has linearizer
  coefficients of radius exactly `R exp(-m sigma)` when
  `0 < sigma < infinity`, and zero when `sigma` is infinite. Corollary
  8.17 then shows that, for any fixed nonzero `Gamma`, the universal
  common-domain property under drift holds iff `sigma = 0`.
- **Theorem 7.23** (source 10). Let `Lambda = diag(e^{2 pi i theta_j})` be
  nonresonant (`lambda^alpha != lambda_j` for `|alpha| >= 2`; repeated
  eigenvalues allowed), `tau = tau(Lambda) < infinity`, and
  `r_ang = dim_Q span_Q(1, theta_1, ..., theta_d) - 1`, so `1 <= r_ang <= d`.
  For any nonzero set-sized `Gamma` and any exact input
  `Lambda z + sum_s t^s f_s` with all `f_s` holomorphic on one polydisk of
  radius `R` and `f_s(0) = 0`, `Df_s(0) = 0`, the normalized conjugacy and its
  inverse have **all** coefficients holomorphic on the open polydisk of
  radius `R exp(-r_ang tau)`, and evaluate to a bijective conjugacy of the
  corresponding finite halo. Corollary 7.32 refines the radius at a given
  exponent to `R_gamma exp(-min(r_ang, ell_S(gamma)) tau)`.
- **Theorem 7.34** (source 10). Universal common-domain linearization holds
  iff `tau < infinity`, and the largest universally guaranteed radius
  satisfies `R exp(-r_ang tau) <= R_univ <= R exp(-tau)`, with equality on
  the right when `r_ang = 1`. Proposition 7.35: for
  `Lambda = diag(lambda^2, lambda^3)`, `r_ang = 1` and `tau = 3 tau(lambda)`,
  so any loss factor `0 < kappa < 1` is attained exactly by a nonscalar
  multiplier.
- **Theorem 7.27** (source 10). At fixed tree complexity `m` the colored
  divisor products grow at exponential rate at most `min(r_ang, m) tau`,
  because at most `r_ang` distinct positive exponential rates can occur
  (Corollary 7.25) and each distinct rate is charged at most `tau` in total.
  The prefactor is finite but not explicit, and not uniform in `m`.

## What is NOT claimed

Section 26 is the consolidated record: **125 numbered items covering the 123
distinct limitations stated by the ten sources**, distributed
11/9/10/14/12/12/10/16/12/17 across sources 01–10, each with its originating
source named. None was merged away or softened. The limitations of sources 08
and 09 are N81–N108 (§26.9), and those of source 10 are N109–N125 (§26.10).
Where two overlap, both wordings are kept. Source 08's scalar-only
limitation (N81) and source 09's nonscalar remark (N97) are kept as stated
and annotated as re-scoped by source 10.
Source 09's own scope limitation (one variable only) is kept as its own
limitation and annotated after the merge rather than dropped. The load-bearing
limitations:

- **Status.** Ten AI-assisted, unrefereed research drafts; the full merged
  report is not proof-assistant verified. The repository now has checked
  Lean proofs of the finite-word support lemma, the corrected combinatorial
  ancestry bounds, and the counterexample above. This partial coverage
  does not certify the operator calculus or the analytic classification
  theorems. None of sources 08, 09 and 10 supplies Lean code, and source
  10's formalization outline is a plan, not an implementation. Priority is
  not certified for any statement, and no named published conjecture is
  claimed solved. Every repository and literature inspection was
  *targeted*, not exhaustive. For sources 08 and 09 in particular, the
  clustering-and-packing estimate is of the same kind as classical
  small-divisor counting (Davie's estimates, discussed by Marmi) and as the
  Fauvet–Menous–Sauzin tree expansions. Source 08 inspected the 2018 tree
  paper at abstract level only, and both sources disclaim priority
  (N94, N105). Source 10 credits the same tree expansions (their 2026
  revision, inspected in HTML) and Carletti's non-Archimedean tree formulas
  (abstract level only), and disclaims priority too (N111).
- **The exact-multiplier answer is sharp only in angular rank one.**
  Theorem 7.13 covers `Lambda = lambda I_d`, and sources 08 and 09 left the
  nonscalar case open because their clustering argument does not apply to
  the divisors `lambda^beta - lambda_j` (§7.6, N81, N97). Source 10's
  Theorem 7.23 covers every exact diagonal unitary nonresonant `Lambda`,
  but its factor `r_ang` is a proved bound, not an optimality claim: for
  `r_ang >= 2` and `0 < tau < infinity` the optimal universal radius is
  undetermined between `R exp(-r_ang tau)` and `R exp(-tau)` (N114).
  Drifting multipliers in several variables, resonant spectra, Jordan
  blocks, nonunitary spectra and infinite coordinate dimension are not
  covered (N120). The prefactor of Theorem 7.27 is not explicit and not
  uniform in the tree complexity (N117). The cyclic theorem is one-variable only; the
  several-variable collapse over a fixed cyclic group is not addressed
  (Question 25.2). `R exp(-tau)` and `R exp(-r_ang tau)` are universal
  guarantees, not formulas for each input. Holomorphy is claimed on the *open* polydisk only, with no
  uniform norm bound and no natural-boundary claim.
- **The exact ball is a valuation ball.** "Exact" means the maximal
  *centered valuation ball* only. It is not the full pointwise summability
  locus, not a maximal non-ball invariant domain, and not every analytic
  continuation. The bounding shell is an algebraic valuation shell. It is
  **not** a topological boundary (valuation balls are clopen) and **not** a
  circle for the ordered-surreal modulus. The common-domain disk is **not**
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
  no sequential completeness. All control is by supports. In sources 08 and
  09 the constants and polynomial exponents depend arbitrarily on the
  support word, and the factor `(C_a n)^m` is harmless only at fixed `m`.
  For `lambda z + t^eta z^2` it becomes `n^n`, so no ordinary convergence
  follows.
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
  critical-scale obstructions are collected in §21 precisely so they
  are not mistaken for one.
- **"Transcendental" and "analytic" are defined terms.** Transcendence is
  over the specific base `C(w)((t^Gamma))`. The coordinate is
  *differentially* algebraic, satisfying `H' = Omega H` with `Omega` in
  that base, so "transcendental" must not be upgraded to "differentially
  transcendental". Nor is it a claim about any individual value lying
  outside `No[i]`. "Analytic" in the Hamiltonian chapter means exactly the
  entire-coefficient Taylor-compatible realization.
- **Uniqueness is gauge-relative** in the Hamiltonian normal form, and
  resonant normal forms are not claimed unique anywhere. In §7, "unique"
  means unique among tangent-to-identity formal coordinates.
- **The quasi-periodic half is a coefficientwise Hahn theory.** It does
  **not** assert convergence after substituting a nonzero real parameter
  for a Hahn monomial, and it **does not improve classical real analytic KAM
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

Section 25 records the eleven open questions in the categories in which
they are open. Two of them are re-scoped by sources 08 and 09, and one of
those again by source 10. Question 25.1 (with its first statement,
Question 8.20) is now settled for every exact diagonal unitary multiplier
and stays open only for the **optimal radius** when `r_ang >= 2` and
`0 < tau < infinity`; Question 25.2 is settled in one variable and stays
open only for the several-variable collapse over a fixed cyclic group. The
three sources add no new question. Their remaining directions are folded
into Questions 25.1, 25.7 and 25.8.
Appendix G is a per-theorem hypothesis audit, and Table 5 is source 09's
own hypothesis-use audit for Theorem 7.13.

## The verification programs

`code/` holds the ten programs unmodified and `data/` their recorded
outputs. Totals where a script prints one: **54** (01), **1,109** (02),
**21** (03), **2,764** (04), **245** (05), **119** (06). Source 07 prints
no total. It checks the slow-circle conjugacy through degree ten, **117**
exact coefficient recurrences, and the stratum classification of **1,330**
integer modes into **1,210 / 110 / 10**. Sources 08 and 09 print no single
total because their units differ:

- Source 08 uses SymPy, exact `Q(i)`, and the multiplier `(3+4i)/5`. It
  checks 7 and 14 component identities for the one- and two-variable
  conjugacies, 6 polynomial identities for the cyclic fold, and 60
  first-block scalar equalities. It also checks **85,660** tree-packing
  inequalities over 8,566 configurations and **119,136** chain inequalities
  over 14,892 chains.
- Source 09 uses the standard library. It checks **83,996** packing cases
  over 8,514 weighted skeletons, 45 tree-count bounds, and one zero-weight
  counterexample. It checks **33,030** clustering cases, 7,075 of them
  nonempty. Its formal algebra makes 270 coefficient comparisons over 2,478
  tree terms and 36 identity groups, with multipliers `2`, `2/3` and `-2`,
  which are **not** on the unit circle.
- Source 10 uses the standard library and exact `Q(i)`. It checks the
  marked-block contraction of Lemma 7.26 on all **2,730** colored tree
  configurations with at most three internal vertices (**18,466** marked
  subsets) and on **1,000** seeded random configurations with four to nine
  vertices, and it checks 8 conjugacy and inverse component identities for a
  two-variable nonscalar example with multipliers `(3+4i)/5` and
  `(5+12i)/13` through parameter degree 3 and spatial degree 6, with 21
  nonzero divisors.

All ten were re-run and all pass. When sources 08 and 09 were integrated,
they were re-run on a copy with Python 3.14.4 and SymPy 1.14.0. Source 08
reproduced its record in every field except elapsed time and Python version,
and source 09 reproduced its record field for field. Source 10 was re-run on
a copy with Python 3.14.4 when it was integrated; its ten printed lines
match `data/10-nonscalar-common-domain-verification_results.txt` line for
line, apart from line endings. Section 24.1 tabulates
exactly what each suite checks and each one's own scope disclaimer. Every
suite prints one, which is a real and unusual discipline in this material.

**Run every suite on a copy, never in this tree.** Four of the ten
scripts rewrite their own evidence:

- source 03's writes `data/verification.json`;
- source 04's writes `data/verification.json` *and* `data/coefficients.csv`;
- source 06's writes `data/verification.json`;
- source 07's takes `--output` with **default** `verification.json`,
  resolved against the current working directory and written with an
  unconditional `write_text`: no existence check, no backup, no dry run. The
  invocation documented in its own README is exactly the one that
  overwrites the delivered record.

Source 01's script prints to stdout, but its Makefile's `verify` target
redirects that stdout over the delivered `verification.txt`. A byte-identity
check performed after an in-place run compares two equally modified copies
and passes while proving nothing.

Sources 08 and 09 are **overwrite-safe**. Without `--output` they print, and
they refuse an existing output path (08 unless `--overwrite` is given, 09
always). Their shipped build helpers still refer to the delivered layout:

- `code/08-exact-and-drifting-multipliers-build.sh` and the `pdf` target of
  `code/09-single-loss-linearization-Makefile` build the standalone source
  manuscripts, which are **not** shipped here;
- the Makefile's `verify` target calls `verify.py` by its delivered name;
- source 08's docstring names `data/verification.json`.

Run them on a copy, for example:

```sh
python code/08-exact-and-drifting-multipliers-verify.py --output /tmp/08-rerun.json
python code/09-single-loss-linearization-verify.py --output /tmp/09-rerun.json
```

Source 10 is overwrite-safe as well: its script takes no arguments, writes
no file and prints ten lines, so `python
code/10-nonscalar-common-domain-verify.py` can be compared directly with
`data/10-nonscalar-common-domain-verification_results.txt`.

**Independently checked, beyond running the suites.** The finiteness bound
of Theorem 17.5 was verified without source 07. Writing the divisor as a
sum of real linear forms against the frequency's Hahn coefficients makes
the level sets intersections of kernels, so a new level appears exactly
when the kernel rank strictly drops — at most `d` times. **400 random
trials** over rational coefficient matrices, with resonances deliberately
forced in 40 per cent of them, gave **zero violations**. A worked instance
at `d = 3` had kernel ranks 2 → 1 → 0 with achieved levels `{0, 1, 3}`,
attaining the bound with two indices skipped exactly where the rank did
not move. Section 24.2 records this.

What the checks are **not**: they are finite exact symbolic identities. They
do not prove Hahn summability, well-founded recursion, arbitrary-rank
support finiteness, ordinary analytic domain preservation, any
small-divisor limsup, the exact convergence radii, the universal
quantifiers, the classification theorems, the algebraicity dichotomy, the
centralizer theorems, the slow-time theorem, the Liouville construction,
the common-radius theorems, the rate-count lemma, the rational-rank product
bound, the cyclic noncancellation along an infinite subsequence, or
novelty. Source 07's checks in particular verify neither the
irrationality of its Liouville constant, nor any infinite-mode
subexponential estimate, nor the word lemma, nor the infinite-support
conjugacy theorem. Source 09's tests do not test the unit-circle estimate at
all. Source 10's 1,000 larger tree configurations are seeded samples, not an
enumeration, and its algebra test checks nonzero divisors only in the
finite range it uses. Sources 03 and 06 truncate by **total parameter or label degree**,
which is explicitly *not* a Hahn valuation cutoff in a higher-rank group.
Fifty of source 05's 245 assertions are finite lexicographic illustrations
for `n = 1..50`, an illustration and **not** the all-`n` proof, which is in
the text. Its verifier also loses one top coefficient on division by
`eps`, so reciprocal and pullback comparisons are checked only through
degree `N-1`. Sources 04 and 07 both list a `SHA256SUMS.txt` in their
READMEs that does not exist in the delivered archive; this is recorded
rather than repaired. Sources 08 and 09 neither ship nor promise one.
Source 10's delivered manifest matched all six delivered files and is not
shipped.

Reproducing a suite requires Python 3.10 or later and, for five of them
(01, 03, 05, 06, 08), SymPy; the pinned version recorded by the sources is
`sympy==1.14.0`. Source 10 needs only the standard library (Python 3.9 or
later, by its own statement).

*Two later reports that share only words.* The formal-flow "autonomous flows"
of this report (see `dyn:warn:embedding`) are unrelated to the autonomous
first-order equations of [differential-equations](../differential-equations/)
Part VI, which concern a scalar derivation on `No[i]`. The global symbolic
dynamics of expanding polynomials `q^{-1}P` is in
[expanding-polynomial-dynamics](../expanding-polynomial-dynamics/); it is a
different subject, kept separate, and answers neither N18 nor N51.

## How to build

Standalone LaTeX with an internal bibliography. No external `.bib` file, no
graphics, no shell escape, no network access.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

A standard TeX Live or MiKTeX installation with the packages named in the
preamble suffices. The recorded build is clean: 0 errors, 0 undefined
references, 0 undefined citations, 0 multiply-defined labels, 0 duplicate
PDF destinations, 0 LaTeX warnings and 0 package warnings, 171 pages. The
three small overfull boxes (at most 3.2pt) and one underfull box predate
source 10. All 651 labels carry the `dyn:` prefix.

## Relation to the rest of the collection

- **Extends** `docs/surcomplex/differential-equations/`. Its
  ordinary-domain monodromy example, an infinitesimal residue invisible to
  ordinary monodromy, is the antecedent of the monodromy exponent
  `rho_a`, and is cited at the point where `rho_a` is introduced. What is
  new here is the torsion lemma, the finite-cover obstruction, the
  classification of algebraic leading coordinates and the dichotomy, not
  the invisibility phenomenon itself. That report's cross-category warning
  is adopted verbatim, once, in place of re-deriving the
  coordinate-versus-surreal-derivation distinction ten times. Source 07
  separates itself from that report **by name**. Its torus derivatives are
  external derivations annihilating the Hahn scalar field, so the
  cohomological equation of §18 is not a surreal differential equation for
  the Berarducci–Mantova derivation, and no theorem of either report
  transfers to the other. It also records that a targeted repository code
  search for "cohomological" returned no match, while stating that this is
  not an exhaustive audit. Sources 08, 09 and 10 likewise use only external
  coordinate derivatives.
- **Inherits from** `docs/surcomplex/analysis/`: the
  no-topological-convergence discipline and the Neumann support material.
  These are cited, not restated. Only one statement of the support lemma is
  kept, and the per-source restatements are deleted.
- **Inherits from** `docs/surcomplex/analytic-geometry/`: the
  four-ring table and its separating witness, neither of which is reprinted.
  Every theorem names its ring in that report's vocabulary, and exactly two
  rows are added (entire coefficients, polynomial coefficients) with the
  note that they are new **rows**, not new rings. Theorem 7.13 decides the
  common-domain germ ring `R_n` of that table for a scalar exact multiplier,
  and Theorem 7.34 for every exact diagonal unitary one, up to the optimal
  radius when `r_ang >= 2`.
- **Adjacent to** `docs/surcomplex/contours-and-stokes/`. It is background
  for the period section and deliberately unused there: every integral is an
  ordinary complex line integral taken coefficient by coefficient over
  ordinary curves in a fixed domain in `C`. A period here is **not** a
  surcomplex contour integral and **not** a residue at a surcomplex point.
- **Kept separate from** `docs/surcomplex/rank-one-berkovich/`, with an
  explicit cross-note (§23.5). That is the one report in the
  collection where convergence is genuine convergence, inside a fixed
  rank-one workspace. This report works at arbitrary rank with a
  deliberately rank-2 example. A Lindahl-type ultrametric disk radius and
  the maximal centered valuation ball here are **different categories**,
  and the exact-ball and shell-periodicity conclusions must not be
  transported to `C_p`. Without that note a reader will read the two
  reports' "disks" as the same object.
