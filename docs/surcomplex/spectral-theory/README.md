# Surcomplex Spectral Theory

**Singular Values, Infinitesimal Rank, Multiscale Stability, and Exact
Determinantal Ramification**

One article, `article.tex` (52 pages compiled), assembled from **two
separately delivered manuscripts**, with `code/` and `data/` holding both
sets of exact symbolic checks and their recorded output.

## Provenance

| file | manuscript |
| --- | --- |
| `01-determinantal-singular-value-scales.tex` | **Manuscript A**, "Surcomplex Spectral Theory: Singular Values, Infinitesimal Rank, and Multiscale Stability". The base: the article was built from this text, and every section except §9–§11 is its. |
| `02-determinantal-ramification-descent.tex` | **Manuscript B**, "Spectral Descent and Exact Ramification in Surcomplex Matrix Calculus" (archive `spectral_descent_surcomplex`), with its README and source audit beside it. Contributes §9–§11 and the removal of the divisibility hypothesis. |

Both are dated 21 September 2026. B cites A by name and explicitly declines
to reclaim its content: "the SVD over real closed fields, determinantal
singular scales, positive Cauchy–Binet identities, and perturbation
theory … are not claimed again as new here." So the shared mathematics is
printed **once**, in A's form — `thm:scales` and `thm:gram` are A's theorems,
and B's re-derivations of them appear only as the one-line corollary
`spec:cor:gramscales`.

The two audited the repository at different pinned revisions, A at
`e260237` and B at `aa84627`, and both declared their audits targeted rather
than line-by-line.

## What the report is

The linear algebra chapter the collection did not have: **finite** matrices
over a real closed field `F` and its complexification `F[i]`, and then over a
set-sized Hahn workspace inside `No[i]`. Every dimension is an ordinary
finite integer. Three halves, really.

**The classical half, without compactness.** Hermitian and normal
diagonalization, positive square roots and congruence, the SVD, polar
decomposition, a generalized Hermitian eigenproblem, operator and Frobenius
norms, Courant–Fischer and Ky Fan variational principles with **attained**
extrema, eigenvalue and singular-value perturbation, Moore–Penrose inverses,
least squares, and best low-rank approximation. The point is the
justification: these need **real closedness, not Archimedean completeness**.
The proofs exhibit the relevant witnesses explicitly, so a maximum is
produced rather than extracted from a compactness argument — which matters
here, because the usual compactness is unavailable and class-sized
compactness questions never have to be raised.

**The scale half.** Over a Hahn workspace a nonzero singular value has a
valuation, and the list of those valuations is extra structure invisible in
an ordinary complex matrix. The synthesis is a pair of theorems:

- *Singular scales are determinantal scales* (`thm:scales`). With
  `Δ_k(A) = min v(det A_{I,J})` over `k × k` minors, `Δ_k = γ_1 + ... + γ_k`
  where `γ_k` is the `k`-th singular valuation. The slopes are
  nondecreasing, and `(γ_1, ..., γ_r)` is a complete invariant for
  equivalence under integral invertible row and column operations. The
  valuation ring need not be Noetherian or discrete — only finitely many
  minors are involved, so the minimum exists.
- *Positive Cauchy–Binet* (`thm:gram`). Writing
  `det(I + s A*A) = Σ c_k s^k`, one gets `c_k = e_k(σ_1^2, ..., σ_r^2)` and,
  crucially, `c_k > 0` and `v(c_k) = 2Δ_k(A)`. **Positivity is what forbids
  leading cancellation**, so the Gram polynomial's coefficient valuations
  give every singular scale, and its standard parts give the leading
  singular amplitudes one scale block at a time — with no eigenvector
  computation and no polygon drawn in an ordinary real plane.

What that buys: an intrinsic rank filtration separating exact rank from
standard-part rank, a root-free minimum-valuation elimination algorithm with
a stated exact-operation contract, precision certificates for singular
scales valid for arbitrary-rank value groups, distance to singularity as an
attained **minimum** rather than an infimum, ordered pseudospectra for
nonnormal matrices, gap-sensitive spectral projectors and subspace
perturbation (with an explicit warning about Gram squaring), Schur-complement
corrections at degenerate clusters, a genuine matrix Hahn-summability
theorem separated from algebraic inversion, regularization read as an
explicit scale filter, and a finite Schmidt/tensor example with
infinitesimal components.

**The arithmetic half (manuscript B).** The workspace convention is now a
set-sized ordered abelian `Γ` that is **not assumed divisible**. Passing to
the divisible hull is harmless for existence and fatal for arithmetic: it
makes every positive square root free, and so erases the distinction between
a matrix whose spectral data need no new scales and one whose positive root
genuinely does.

- *Spectral descent* (`spec:thm:hermitian`, `spec:cor:normal`,
  `spec:thm:svd`). Hermitian and normal diagonalization and the SVD exist
  over `K_Γ` with **every exponent in the subgroup generated by the input
  exponents**, by a finite splitting tree of at most `n−1` nontrivial nodes
  — a bound independent of the order type of the supports and of the rank or
  cardinality of `Γ`. The infinite series are licensed by strong Hahn
  summability and a Higman-type word-finiteness lemma (proved here, not
  cited), never by convergence.
- *The determinantal ramification law* (`spec:thm:ramification`). For
  positive semidefinite `A` of rank `r` and any `q ≥ 2`,
  `K_Γ(A^{1/q}) = K_{Γ + Σ_k Z·Δ_k(A)/q}`, of degree `|R_q(A)| ≤ q^r` where
  `R_q(A)` is the subgroup the classes `Δ_k + qΓ` span in `Γ/qΓ`; finite,
  abelian, **totally ramified**, with Galois group `Hom(R_q(A), μ_q)`. So
  `A^{1/q}` is defined over `K_Γ` **iff** every `Δ_k(A)` lies in `qΓ`, and
  the degree is computed from finitely many minor valuations with no
  eigenvalue and no eigenbasis. The same invariant that measures singular
  scales controls a finite radical extension.
- *The exact Gram criterion* (`spec:cor:gramcriterion`). `A = C*C` with `C`
  over `K_Γ` iff `Δ_k(A) ∈ 2Γ` for all `k` — necessary for every rectangular
  Gram representation, and `C` may be taken square.
- *The primitive trace* (`spec:thm:primitivetrace`). The single scalar
  `tr(A^{1/q})` generates that entire extension, and so does any
  `Σ a_j λ_j^{1/q}` with `a_j` **strictly positive** in `F_Γ`. Proved by a
  mechanism, not by genericity: positivity keeps every needed coset of
  `Λ/Γ` visible, so the *specific* unweighted trace never degenerates.
- Plus finite-witness simultaneous diagonalization (`spec:thm:simultaneous`),
  joint ramification for several roots with no commutation assumed
  (`spec:cor:joint`), an order-preserving transport proposition, and the
  surcomplex transport `spec:cor:surcomplex`, which reads all of this off the
  **exact** input support group `H` rather than its divisible hull.

### What still needs divisibility

`spec:rem:divisibility` says it in one place: the Schur triangularization of
a non-normal matrix (`prop:normal`), the positive square root of an
arbitrary positive semidefinite matrix with the Cholesky factorization and
generalized eigenproblem built on it (`prop:positive`), and obtaining all eigenvalues
of an arbitrary square matrix. These constructions can be carried out in `Γ ⊗ Q`. The exact cost
computed by `spec:thm:ramification` concerns principal positive matrix roots,
not the splitting field of an arbitrary matrix. The pseudospectrum over
`K_Γ` and its perturbation characterization remain valid without divisibility. Everything
else — the Hermitian and normal spectral theorems, the SVD, the polar
decomposition, every norm and variational principle, `thm:scales`,
`thm:gram`, the rank filtration, the scale algorithm, the perturbation
certificates, `thm:series` — holds over an arbitrary `Γ`.

### The anti-theorems

These are the most valuable thing B brings to a report that worked where
they were invisible, and they are kept in full.

- The raw input **monoid** is not preserved, only the subgroup:
  `spec:ex:monoid` has input exponents 3 and 4 and an eigenvalue exponent 5.
- Degrees can **drop** under enlargement of the base group
  (`spec:warn:degreedrop`): `Z ↪ Q` kills all ramification. Degree is
  preserved under isomorphism onto the image, not under enlargement.
- A Gram witness can use a **larger group than its own product**
  (`spec:ex:gramwitness`) — which is why every statement names both the
  matrix and the base group.
- `(x, y; y, −x)` has **no eigenvalue in `C[[x,y]]`** (`spec:warn:crossing`),
  so this is explicitly not a multivariable analytic eigenbasis theorem.
- Partial sums need not converge even when the Hahn identity holds
  (`spec:ex:nonconvergence`), so a remainder bound is never used as a
  convergence proof.
- Positivity cannot be dropped from the trace theorem
  (`spec:warn:positivity`): the signed root `diag(t^{d/2}, −t^{d/2})` is a
  Hermitian square root generating a quadratic extension whose trace is
  **zero**.
- Membership in `qΓ` is extra group data and need not be decidable from
  black-box order comparison (`spec:warn:qgamma`), so the exact criterion
  `Δ_k ∈ qΓ` may be unevaluable by a representation that can compute every
  `Δ_k`.

### Which spectrum this is

`§1.5` fixes the word once. Here *spectrum* is the algebraic **eigenvalue
list** of a finite matrix, with the valuations of eigenvalues and singular
values. It is **not** the differential *phase spectrum* of
[`differential-equations`](../differential-equations/), a multiset of purely
infinite surreal parts of primitives of eigenvalues — not numbers of the same
kind, and not finite angles. It is **not** the *prime spectrum* of a ring,
the sense in which [`analytic-geometry`](../analytic-geometry/) discusses
maximal and prime ideals. And the visible-rank levels `r_{<θ}, r_{≤θ}` of §12
are a list of scales, not a spectrum in any of those senses.

## Where it sits among the existing reports

It can be read **independently of the analytic coefficient-ring machinery** —
unusually for this family, the `analysis` and `analytic-geometry`
prerequisites do not apply. What it needs is the workspace convention: fix a
set-sized `Γ` and work in `K = C((t^Γ))`, licensed by the localization
theorem in
[`foundations`](../../foundations-and-computation/foundations/) (every *set*
of surcomplex numbers already lies in one such workspace). The article keeps
ordered magnitude, Hahn valuation, strong summability and workspace-relative
topology as four separate structures, and its matrix series theorem is
explicitly *not* a claim of fine-topological convergence — consistent with
[`analysis`](../analysis/), where every set of surcomplex numbers is closed
and discrete in the fine topology.

- [`polynomial-algebra`](../polynomial-algebra/) is the closest neighbour and
  the intended bridge: its Newton profiles of scalar polynomials are what
  `thm:gram` feeds, via the Gram polynomial `det(I + s A*A)`. The adjacent
  matrix ingredients it already carries — an algebraic Schur inequality, the
  differentiating compression, Hermite signature counting — are cited rather
  than re-proved. Its *rootwise* condition number is a different object from
  the matrix condition numbers here, and the two should not be conflated.
- [`finite-deformations`](../finite-deformations/) also has Gram matrices,
  but they are **residue** pairings in a finite free Frobenius algebra
  (`det Gram` a unit even where the discriminant vanishes). Those are not the
  positive-definite Hermitian Gram matrices of this article, and no theorem
  transfers between them.
- [`differential-equations`](../differential-equations/) uses eigenvalues of
  constant complex matrices for its non-oscillation results. That is a
  different use of spectra — over `C`, not over `K` — and nothing here is
  needed to read it. Its *phase spectrum* is a different object again; see
  above.
- [`computer-algebra`](../../foundations-and-computation/computer-algebra/) is
  where the exact-operation contracts belong: §13.2, which operations a
  symbolic scalar representation must supply for the scale algorithm to run;
  §13.4, why finite truncation cannot certify every exact rank; and
  §13.3, the strictly harder contract for the splitting-tree construction
  together with `spec:warn:qgamma`. That report's own inventory already makes
  a related distinction on the implementation side: a fixed rational exponent
  lattice permits fractional exponents that a fixed integer lattice may lack.
  This is only an exponent condition. Even `sqrt(1+t)` has integer exponents
  but requires an algebraic or series representation beyond rational functions.
  This cross-reference does not claim to solve that
  report's representation or computability problems.

## Scope of the historical coverage audit

The original audit at `e260237` compared the catalogue, the polynomial report's
inventory and opening sections, and nearby matrix material. It distinguished
polynomial-root tools and residue pairings from this report's systematic SVD,
conditioning and singular-scale development. That targeted reading explains
why this report was added; it does not prove that every other source lacked
every relevant theorem. The collection has since expanded, including Hermitian
spectral arguments in differential equations and surquaternions. Consult the
current reader map and local hypotheses when transferring those results.

## What it does not claim

Every limitation both manuscripts shipped with is kept here.

- A rigorous integrated exposition with a non-Archimedean interpretation.
  **No priority claim**, and no claimed solution of a named open problem —
  manuscript B's status box says it "selects the new theorems alternative in
  the request, not a claimed solution of a named published open problem".
  Real-closed-field spectral theory, the SVD, low-rank approximation,
  pseudoinverses and classical perturbation theory are **not** presented as
  new; nor is priority claimed for the determinantal/valuation consequences.
  The arbitrary-rank determinantal and primitive-trace package is offered as
  a *candidate original contribution* from a targeted, admittedly
  non-exhaustive search; **priority is not certified**.
- Predecessors are conceded, not displaced: Adkins 1991 (normal matrices over
  hermitian DVRs), Keller–Ochsenius 1995 (iterated real Laurent-series fields
  and one infinite-rank Hahn field), Parusiński–Rond 2020, and the February
  2026 preprint arXiv:2602.08313 (Dai–Liang–Lu–Zhi). Neither "a spectral
  theorem beyond `R`" nor "no fractional exponents in a Laurent-series
  eigenbasis" is claimed as new, and the Hahn support foundations are
  standard Hahn–Neumann and word-order ideas, reproved only for
  self-containment.
- No infinite-dimensional operator theory: no Hilbert spaces over `No[i]`,
  bounded-operator spectra, compact or trace-class operators, spectral
  measures.
- No global analytic choice of eigenvectors through collisions or across
  multiple parameters, and no removal of the obstructions in the
  multivariable formal power-series category — see `spec:warn:crossing`. What
  *is* now proved is the support-controlled construction for a **single**
  matrix over an arbitrary value group.
- Not effective. The exact decompositions do not by themselves give
  algorithms for arbitrary surreal inputs. The splitting tree is a finite
  tree of **set-valued** support data, not a finite list of monomials — one
  node can carry an uncountable well-ordered support — and exact zero tests,
  support access and leading-coefficient extraction must be supplied by the
  representation. `thm:series` is a strong-summability statement, not
  fine-topological convergence.
- The coefficient fields remain the full `R` and `C`; preservation of a
  smaller coefficient field such as `Q` is **not** asserted.
- All matrix dimensions are ordinary finite integers, and all field and
  extension statements are set-sized. No proper-class sums or class-sized
  Hahn workspaces anywhere.
- The symbolic checks exercise the listed finite identities on their stated
  inputs. They do **not** machine-verify the general proofs, arbitrary Hahn
  supports, arbitrary ordered groups, the proper-class foundations, or an
  effective representation of all surreal numbers. Exact symbolic zero tests
  are not replaced by truncation. Assertion counts include individual zero
  coefficients and are **not** counts of independent theorems. The original
  source reports did not supply a complete proof-assistant formalization.
  The current [coverage ledger](../../FORMALIZATION.md) separately maps checked
  prerequisites and source claims; §20's proposed dependency order is not
  evidence that the whole spectral package has been compiled. These are AI-assisted
  drafts, not refereed. B's PDF metadata names its author as "OpenAI,
  research assistance for Vladimir Reshetnikov".
- The audits behind both manuscripts were targeted. A's
  (`repository-audit.md`) inspected the catalogue, `polynomial-algebra`'s
  full inventory and the opening of its source, and the opening of the
  `foundations` README. B's own source audit, delivered with the
  manuscript, inspected the repo map, the main README, the full spectral
  README, and selected visible material of the differential-equations article. Neither was
  line-by-line, and neither treats a search returning no matches as proof
  that a topic occurs nowhere.

## Proof review: 22 September 2026

The main mathematical reading followed finite Hermitian geometry, variational
principles, determinantal scales, support-controlled splitting, ramification
and primitive traces, then the stability and matrix-series applications.
The maintained revision clarifies the following boundaries:

- The Gram-factorization criterion uses `2Γ`; `qΓ` controls the principal
  `q`th root. Root-field sums use only `1 ≤ k ≤ rank A`, avoiding the added
  infinite valuations of vanishing higher minors.
- Perturbation statements explicitly retain Hermitian inputs and orthogonal
  projectors. Zero norm squares and the empty Ky Fan sum are treated separately.
- The finite-precision rank obstruction assumes `Γ ≠ {0}`. For the trivial
  group, truncation through zero gives every coefficient.
- The elimination contract includes valuation extraction. Exponent permission
  and full root representation are distinct computational requirements.
- The hypothesis ledger now lists actual assumptions and proof mechanisms in
  their respective columns, including the arbitrary-group scale theorems.
  `O_v(β)` consistently takes an exponent threshold.

Historical verification code and data are unchanged. Imported foundational
results and any complete formalization remain separate from this proof review.
The historical symbolic suites were not rerun for this documentation revision.
The corrections received a second independent review.

## Build

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
latexmk -c
```

Run from **this** directory. A standard TeX Live or MiKTeX installation with
the packages named in the preamble (AMS, Latin Modern, microtype, geometry,
booktabs, tabularx, longtable, xcolor, enumitem, fancyhdr, titlesec,
hyperref, aliascnt, cleveref) is sufficient. The bibliography is embedded;
there is no BibTeX step, no external figure asset, no custom font, and no
shell escape. Without `latexmk`, run `pdflatex` three times. Last build:
**52 pages**, 0 errors, 0 undefined references or citations, 0 multiply
defined labels, 0 LaTeX warnings, 0 overfull and 0 underfull boxes. The revised
three-pass build removes the baseline's overfull filename line; changed pages
were rendered and inspected.

Neither manuscript's build script works from `code/`. Both pairs
(`code/build.sh`, `code/build.ps1` and their `02-` prefixed counterparts)
`cd` to their own directory before invoking `latexmk article.tex`, and
`article.tex` is in the parent. They were written for the flat delivery
layouts — use the command above instead. B's README says its `build.ps1` was
supplied for convenience and was not executed.

## Rerunning the finite checks

**Run these on a copy of the directory, or redirect the output.** Both
scripts default their output directory to `../data`, so running either in
place writes report files into the directory that ships the recorded
evidence:

```sh
python -m pip install -r data/requirements.txt                       # sympy==1.14.0
python code/verify-examples.py --output-dir "$TMPDIR/spectral-check"
python code/02-determinantal-ramification-descent-verify.py \
       --output-dir "$TMPDIR/spectral-check-2"
```

Python 3.9 or newer. No floating-point sampling is used anywhere; A's matrix
generator uses the fixed seed `20260921`, and so does B's finite-quotient
enumeration.

The default path is the destructive one in both cases, and nothing in either
script warns about it. B's own README does suggest `--output-dir
rerun-results`, but the argparse default is
`Path(__file__).resolve().parents[1]/"data"` and the two report files are
written there unconditionally. In this repository the ingest renaming happens
to blunt the hazard rather than fix it: B's script writes bare
`verification.json` and `verification.txt`, while the shipped evidence is at
`data/02-determinantal-ramification-descent-verification.{json,txt}`, so a
bare run **adds** files beside the recorded ones rather than replacing them.
The same is true of A's script, which writes underscore filenames while the
delivered evidence was renamed to hyphens. Do not rely on that: run on a copy
or pass `--output-dir`.

What is recorded, and what has been rerun:

- `data/verification-report.json` and `.txt` are **A's** delivered run:
  **176 exact assertions across 18 matrix-profile cases, PASS**, under
  Python 3.13.5 and SymPy 1.14.0. It was rerun for this collection and passed
  again with the same figures under Python 3.14.4 and SymPy 1.14.0.
- `data/02-determinantal-ramification-descent-verification.json` and `.txt`
  are **B's** delivered run: **PASS, 807 exact scalar assertions** — 378
  projector and polar-series coefficients, 144 finite ramification-group
  checks, 105 rational-matrix checks, 96 character checks, 55 block and
  low-degree terms, 29 displayed identities — across 48 finite quotient cases
  and six rational 3×3 positive semidefinite profiles, with a 3×3 Hermitian
  projector and polar construction checked through formal degree 6 over 1674
  nonzero residue-path contributions. Recorded under Python 3.13.5 and SymPy
  1.14.0. It was **rerun for this collection with an explicit output
  directory and reproduced PASS with exactly 807 assertions and the identical
  category split** under Python 3.14.4 and SymPy 1.14.0 (33.7 s).
- Both shipped JSON files still record Python 3.13.5, because they are the
  delivered artifacts and were deliberately not overwritten.

A's valuation and elimination kernel is restricted to `Q(i)(t,u)`, with
`v(t) = (0,1)` and `v(u) = (1,0)` ordered lexicographically — so `u` is
smaller than every positive finite power of `t` in the corresponding Hahn
interpretation. The **least** polynomial monomial, not SymPy's default
leading monomial, determines the Hahn valuation. The two-by-two spectral
examples are checked separately with exact square-root expressions.

## Shipped-layout notes

Files were renamed on ingest, and text carried over from the manuscripts
still names their delivery paths.

- The historical `repository-audit.md` uses `code/verify_examples.py` and
  `data/verification_report.json`. The maintained Appendix B now uses the
  actual paths `code/verify-examples.py` and `data/verification-report.json`.
- B's §12.2 names `code/verify.py`, `data/verification.json` and
  `data/verification.txt`; the files carry the
  `02-determinantal-ramification-descent-` prefix.
- `data/build-report.json` is A's, as delivered, and records
  `pdf_bytes: 492771`, which no longer matches the `article.pdf` beside it:
  the PDF is rebuilt on ingest, as every PDF in this collection is, and the
  article has since grown by a merge. Its `article_source_bytes: 88965` was
  exact for A's text as delivered.
  `data/02-determinantal-ramification-descent-build-report.json` is B's, and
  records its own delivered build: pdfTeX from TeX Live 2025/dev/Debian, 3
  passes, 26 pages, 0 TeX errors, 0 package warnings, 0 overfull or underfull
  boxes, 0 unresolved references.
- Both delivery notes list a `MANIFEST.sha256` that was not carried into the
  repository; in B's case no such file was present in the delivered package
  at all. File hashes are not reproduced here.
