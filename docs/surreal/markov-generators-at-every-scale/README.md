# Surreal Markov Generators at Every Valuation Scale

**Stochastic retracts, prescribed effective chains, relative stability, and rank-one realization**
Single-source research report, 22 September 2026, built from one manuscript
(batch 18, number 14, archive `surreal_markov_hierarchies`). Prepared for
Vladimir Reshetnikov. An AI-assisted research draft, not refereed. The
[Lean ledger](../../FORMALIZATION.md) records proved algebraic clauses of the
resolvent identity, projection-flag construction and irreducible completion;
residue calculations and the remaining hierarchy theorems are pending.

This directory holds one manuscript. It is not a merge. There was no second
source, and nothing here was selected out of a larger body of work.

```
article.tex        the report, standalone LaTeX with an internal bibliography
                   (delivered as surreal_markov_hierarchies.tex, renamed on placement)
article.pdf        the compiled report, 33 pages
README.md          this guide
SOURCE_AUDIT.md    the manuscript's own repository and literature audit, as delivered
code/verify.py     exact finite checks (Python, fractions and SymPy)
code/build.sh      the manuscript's build script, as delivered; does not work as placed
data/verification.json     recorded output of code/verify.py
data/build_validation.json the manuscript's own build record, as delivered
data/requirements.txt      the SymPy pin, as delivered
```

`SOURCE_AUDIT.md`, everything in `code/` and everything in `data/` are
byte-identical to the delivered files. `build.sh` was delivered at the top of
the package and `requirements.txt` next to it. On placement they moved to `code/`
and `data/`. The delivered PDF and README are not shipped.

Every label in `article.tex` carries the prefix `markov:`. There are 116 labels:
the manuscript's 100, each renamed from `x` to `markov:x`, and 16 added on
placement. None was dropped. No label of any other report was touched. The added
material was placed so that every theorem, equation and section number of the
manuscript is unchanged. The numbers below are checked against the build of
`article.tex` in this directory.

## What the report claims

**Setting.** `Γ` is a nonzero, set-sized, **divisible** ordered abelian group,
`F = R((t^Γ))` and `K = C((t^Γ))`. A finite strongly connected digraph on
`n ≥ 2` states carries rates `q_e ∈ F_{>0}`. `L` is the row Laplacian, and the
generator in the usual sign convention is `−L`. The object of study is the
**normalized resolvent** `R_L(s) = s(sI + L)^{-1}` for `s > 0`, taken as a
rational-algebraic definition. Its residue matrix at scale `α ∈ Γ` is
`K_α(c) = res R_L(c t^α)` for real `c > 0`; the article calls it the *shadow*.
The Hahn calculations use finite algebra in one set-sized workspace; the
effective chains use ordinary real matrix limits and exponentials. The surreal
form comes through the normal-form embedding `t^γ ↦ ω^{−γ}`.

1. **Every scale and every marked entry** (Theorem 4.1, `markov:thm:leading`).
   The residue matrix is `N_α(c)/D_α(c)`, built from minimal-weight in-forests.
   The same forest data give the valuation and the leading coefficient of
   *every* resolvent entry, including entries whose residue is zero.
   Proposition 4.2 is a remainder certificate that does not depend on `c`.
2. **A finite projection hierarchy** (Theorem 5.2, `markov:thm:flag`). There are
   at most `n − 1` critical scales. The plateaux are distinct stochastic
   idempotents `I = P_0, P_1, …, P_m = 1π_0` with
   `P_i P_j = P_j P_i = P_max(i,j)` and strictly decreasing ranks. The article
   calls this nested chain a *flag*.
3. **Every crossover is a real Markov chain** (Theorem 6.2,
   `markov:thm:effective`). On the canonical stochastic retract `P = UV`,
   `VU = I` of Lemma 6.1, `K_α(c) = U c(cI + G_α)^{-1} V`. Here
   `G_α = (V K_α(1) U)^{-1} − I` is a real Markov row Laplacian whose zero
   eigenvalue is semisimple. No reversibility, simple-eigenvalue or
   unique-minimizing-forest assumption is made. Corollary 6.3 gives the real
   semigroup `S_α(u) = U e^{−uG_α} V`, whose Laplace transform is `K_α(c)`.
4. **The converse, and a classification** (Theorems 7.1 and 7.4, Lemma 7.2,
   Corollary 7.5). Take any flag of distinct stochastic idempotents ending in
   rank one, any compatible real effective generators (Definition 7.3), and any
   prescribed scales `α_1 < … < α_m` in `Γ`. An irreducible Hahn row Laplacian
   realizes exactly those crossovers and residue matrices. Its rates can be
   taken finitely supported, or positive monomials. Intermediate-scale
   positivity corrections add no crossover. So the forward conditions are
   necessary and sufficient. Proposition 7.6 treats the reversible case with
   full-support residue stationary law, where the plateaux are weighted nested
   partitions. Its converse prescribes a strictly coarsening chain from the
   discrete partition to the one-block partition, a strictly positive real
   probability row, and strictly increasing crossover scales.
   Example 11.1 shows that the full-support hypothesis is needed.
5. **Uniform relative stability** (Theorem 8.1, `markov:thm:stability`). If
   every rate has a relative error of valuation `≥ δ` on the same graph, then
   every resolvent entry has a relative error of valuation `≥ δ`. This holds
   uniformly in `s > 0`, with no spectral-gap loss, and includes entries whose
   residue is zero. Example 8.3 shows that it is sharp. Corollary 8.2 says that
   the leading edge data determine the whole hierarchy at every scale.
6. **Rank-one realization** (Theorem 9.2, `markov:thm:rank-one`). A real
   one-parameter monomial model `a_e x^{ℓ(γ_e)}` reproduces the whole finite
   marked-forest leading diagram. So finite leading data cannot certify higher
   rank. Example 9.4 shows why the finiteness qualification is needed.
7. **Surcomplex eigenvalue amplitudes** (Theorems 10.2 and 10.3,
   `markov:thm:char`, `markov:thm:convexity`). At a critical scale,
   `det(cI_p + G_α) = c D_α(c) / b_{k−}`. Exactly `p − q` nonzero eigenvalues of
   `L` have valuation `α`, counted with algebraic multiplicity. Their normalized
   leading coefficients are exactly the nonzero eigenvalues of `G_α`. So the
   effective characteristic polynomial gives the **leading surcomplex eigenvalue
   amplitudes, including tied scales and nonreal eigenvalues**, and every nonzero
   eigenvalue has `v(Re λ) = v(λ)`. The forest profile is convex, its increments
   are the valuations of nonzero eigenvalues with multiplicity, and at a critical
   scale every intermediate forest size is active. Eigenvalues are those of `L`,
   not of `−L`.

## What the report does not claim

These are the manuscript's own limitations. Each is stated where it applies in
the article, and all are collected in Section 1.4 as (N1)–(N11).

- **No global surreal matrix exponential.** The report works with the normalized
  resolvent. It constructs and assumes no global surreal exponential and no
  surreal heat semigroup. `S_α(u)` is a real semigroup, not the residue of a
  global `exp(−u t^{−α} L)` (Remark 6.4).
- **No path measures, sample paths or stochastic integration.** It also treats
  **no infinite state spaces**: no countable state spaces, no time-inhomogeneous
  rates, no uniform estimates as `n → ∞` and no large-deviation hierarchy. For
  measures and probability, the collection's report is
  [`hahn-valued-measures-and-probability`](../hahn-valued-measures-and-probability/).
  This report does not depend on it, and it does not depend on this report.
- **No countable convergence in the full surreal topology.** All proofs are
  finite algebra in a set-sized workspace. Residue is a ring homomorphism, not a
  limit, and limits in `c` or `u` are ordinary real limits (Remark 2.1).
- **Divisibility of `Γ` is assumed throughout.** No statement is claimed for a
  nondivisible value group. Section 2.3 lists where divisibility is used:
  candidate critical scales `(h_ℓ − h_k)/(ℓ − k)`, the intermediate scales
  `β_j` of Theorem 7.4, the rational span `W` in Section 9, and algebraic
  closedness of `K` in Section 10.
- The bound `n − 1` bounds the resolvent crossover scales only. It does not bound
  the path-event or transition-graph hierarchies of the metastability
  literature.
- Rank-one realization preserves finite leading data only. It does not preserve
  complete series, all inequalities, or the ordered group.
- Stability needs positive rates on one fixed graph. A new edge is not a relative
  perturbation, and the theorem is not an arbitrary-matrix condition-number
  bound.
- The leading spectrum need not be real, and no diagonalizability is claimed.
- Forest enumeration is finite (at most `n^n` parent assignments), not
  efficient, and needs exact comparison of the input data.
- **Credited, not claimed:**
  - the matrix-forest theorem (Chebotarev–Agaev);
  - stochastic-idempotent structure (Dyer–Greenhill–Ullrich);
  - nonreversible metastability and rank-one optimal-forest exponents
    (Gan–Cameron, Freidlin–Wentzell);
  - aggregation (Yin–Zhang);
  - hierarchical Laplacians (Bendikov–Krupski);
  - generalized ultrametric matrices (Nabben–Varga);
  - higher-rank Hahn specialization (Joswig–Smith).

  The reversible partition case and the sign-separation lemma are not
  proposed as new.
- The package is a **candidate original contribution** after a targeted,
  non-exhaustive literature comparison. **Priority is not certified.** The 18
  archives in `docs/new` at the manuscript's pin were not expanded. The three
  further questions of Section 12.4 are open. The finite checks do not prove the
  general theorems.

## Words used differently elsewhere

Section 2.4 of the article fixes these once. In prose that spans several
reports, use the plain names given here.

- *Shadow* is the residue matrix `K_α(c)`. It is not the "shadow topology" of
  `docs/NOTATION.md`, which is the standard-part topology. `res` is the scalar
  standard part `st`, applied entrywise.
- *Flag* is the chain of plateau idempotents of Theorem 5.2 (`markov:thm:flag`).
  It is unrelated to the radical flag of the multiscale theta-series material in
  `surcomplex/hahn-tate-uniformization`.
- *Profile* is the forest profile, where `h_k` is the minimal forest weight.
  `D` and `D_α` are forest denominators. These letters mean other things in
  other reports.
- *Resolvent* is the normalized `s(sI + L)^{-1}`, not the unnormalized
  `(ζI − A)^{-1}` of the spectral reports.

## Relation to the neighbouring reports

**`surcomplex/polynomial-algebra`.** Lemma 10.1 is the case `P = D(s)`, the
forest polynomial, of that report's Newton root-valuation rule
(`polynomial:thm:newton`, Theorem 9.1 there) and of its initial-polynomial root
count with profile formula (`polynomial:thm:initialroots`, Theorem 8.2 there,
equation `polynomial:eq:profileproduct`). The two reports use the same kind of
workspace. The direct proof is kept here (Remark 10.5). Theorem 10.3 goes beyond
the general rule. For a rate matrix every coefficient point `(k, h_k)` lies on
the lower boundary, and every intermediate index is active. Positivity is what
rules out the general behaviour.

**`surcomplex/spectral-theory`.** Its positive Cauchy–Binet identity
(`thm:gram`, Theorem 8.1 there; the label has no report prefix) shows that
positivity forbids leading cancellation for squared minors of a Gram matrix.
Here the same mechanism works for positive forest weights of a row Laplacian
(Remark 3.3, Section 1.5). The matrix classes differ: Gram matrices are
Hermitian, while row Laplacians are generally not normal and can have nonreal
eigenvalues. Neither result implies the other. "Spectrum" in Section 10 has that
report's sense, fixed in `spec:sec:spectrumword`: the eigenvalue list of a
finite matrix over `K` with its valuations. At the placement snapshot
`e9a9650`, the reported search found only one other occurrence of "stochastic"
in the collection's LaTeX, apart from bibliography titles: a proof remark there. It follows its Frobenius eigenvalue bound (`thm:HW`, Theorem 5.3
there) and says the proof does not use a doubly stochastic decomposition.

The theorem numbers of other reports quoted here are from their PDFs as committed
at `e9a9650`.

**`surreal/hahn-valued-measures-and-probability`.** This is the collection's
measure and probability report. Neither report depends on the other. The path
measures and infinite state spaces excluded here are not supplied by an appeal
to it.

[matrix-scaling-at-surreal-scales](../matrix-scaling-at-surreal-scales/) uses
the same no-cancellation mechanism for spanning-tree sums (`scale:thm:tree`);
its deletion gap gives relative gains for a fixed-margin normalization
(`scale:thm:sharp`), unlike this report's gain-free stability bound. The two
concern different maps.

## Stale repository statements, corrected

The manuscript's audit is pinned to `4cf691c`. Two of its statements have since
been overtaken. The article keeps the pin as provenance and adds a "Since the pin"
paragraph to Section 1.3. `SOURCE_AUDIT.md` is kept as delivered, so it still
describes the repository at the pin.

- *"The 18 ZIP archives then in `docs/new` were not expanded."* Every one of
  those archives, and this manuscript, has since been placed in the collection
  and removed from `docs/new`.
- *"An indexed repository search for Markov returned no matches."* At
  `e9a9650`, a full-text search of every LaTeX source in the collection finds
  `Markov` and `metastab` only in this report. `stochastic` also occurs in the
  spectral-theory proof remark noted above.

One description of the checks was also made exact. The article had said that the
program checks "equality of its increments with the critical scale multiset".
The program compares the set of distinct increments with the set of critical
scales, and it checks the ranks of all plateaux and reconstructed generators.
Section 12.2 now says so.

## Build and reproduce

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

This build of `article.tex` gives 33 pages with no errors, no undefined or
multiply-defined references or citations, no duplicate PDF destinations, and no
LaTeX, package or box warnings. The source needs no external figures and no
bibliography database.

`code/build.sh` is kept as delivered, and **it does not work as placed**. It
changes into its own directory (`code/`) and builds `surreal_markov_hierarchies.tex`,
which no longer exists. Use the `latexmk` command above instead. The delivered
record in `data/build_validation.json` (28 pages, Python 3.13.5, SymPy 1.14.0)
describes the manuscript's own build. The current page count also includes the
material added on placement and the subsequent proof review.

`code/verify.py` **overwrites `data/verification.json`**, since it writes to
`../data/` relative to its own location. Run it on a copy of this directory:

```sh
# from docs/surreal/; any scratch location will do
cp -r markov-generators-at-every-scale /tmp/markov-check
cd /tmp/markov-check
python -m pip install -r data/requirements.txt              # SymPy 1.14.0
python code/verify.py
```

The program uses exact rationals and SymPy, a fixed seed (`20260922`), no
floating point and no network. It fails with an assertion error if a check
fails. The recorded run, `data/verification.json`, reports `PASS` for 48
complete digraphs, 12 each on 2, 3, 4 and 5 vertices. Valuations are in
lexicographic `Q²`. The run enumerated 17,280 in-forests and checked 105
critical kernels, plus seven symbolic checks:

- the three-state example;
- the projection-flag inverse;
- the irreducible completion;
- a four-state forest identity;
- the sharp relative error;
- the prescribed-crossover construction;
- the absence of a new crossover at the positivity-correction scale.

A rerun on a copy at placement took about four seconds under Python 3.14.4 and
SymPy 1.14.0. It reproduced the recorded file exactly, apart from the line
endings the operating system writes. These are finite checks. They are not a
proof of the general theorems. The algebraic Lean coverage is described above.

## Provenance

The source is one manuscript, *Surreal Markov Generators at Every Valuation
Scale*, dated 22 September 2026. It arrived with the delivery committed as
`15d4bab` and was placed at `e9a9650`. Its repository comparison is pinned to
`4cf691c7d951e037739d32d9f5c387dcce724f3c`. With one source there were no merge
decisions. Every theorem, proof, example and disclaimer is kept.

Placement made the following changes:

- It added the label prefix and Sections 1.4 (non-claims), 1.5 (neighbouring
  reports), 1.6 (provenance), 2.3 (divisibility) and 2.4 (words).
- It added Remarks 3.3 and 10.5, which point to other reports, and a definition
  of "shadow", a word the manuscript used without defining.
- It added the divisibility pointers in Sections 9 and 10, the "Since the pin"
  paragraph, and the rerun note in Section 12.2.
- It added the AI-assisted-draft status and the divisibility and path-measure
  sentences to the abstract and status paragraph.

Placement left the mathematics unchanged, as recorded in Section 1.6 of the
article. The subsequent corrections are recorded below.

## Subsequent proof review

The maintained article now makes the workspace construction valid even for
purely real inputs: adjoin exponent `1` before taking the rational span. A finite
input can have infinite normal-form supports; only the leading edge exponents
span the finite-dimensional space used for rank-one specialization. The
valuation-error convention includes `O_v(+∞) = 0`, as needed when a remainder
vanishes exactly.

The review expands the transient-block decay estimate, the effective-generator
inverse at the repeated parameter, the spectral real-part argument, and
invertibility at the prescribed crossover. It also clarifies that critical
scales are valuations of **nonzero eigenvalues**; valuation zero is allowed.
The matrix-forest import was checked against Propositions 2 and 3 of
[Chebotarev–Agaev v2](https://arxiv.org/abs/math/0508178v2), including its
row-Laplacian and in-forest orientation. This review does not certify the other
literature comparisons or priority claims.

A review rerun under Python 3.13.14 and SymPy 1.14.0 passed all 48 instances
(17,280 forests and 105 critical kernels) and all seven symbolic checks. Its
JSON content matches the delivered record. The copied program and build files
were unchanged, and the maintained article rebuilt in three passes to 33 pages
without warnings or box issues. These counts describe finite checks, not
coverage of every theorem.
