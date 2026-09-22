# Surcomplex Spectral Theory

**Singular Values, Infinitesimal Rank, and Multiscale Stability**

One standalone research article, `article.tex` (30 pages compiled), with
`code/` and `data/` holding the exact symbolic checks and their recorded
output. Not a merge: it has no `sources/`.

## What the report is

The linear algebra chapter the collection did not have: **finite** matrices
over a real closed field `F` and its complexification `F[i]`, and then over
a set-sized Hahn workspace inside `No[i]`. Every dimension is an ordinary
finite integer.

Two halves, and the second is the reason the first is worth writing down.

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

## Where it sits among the existing reports

It can be read **independently of the analytic coefficient-ring machinery** —
unusually for this family, the `analysis` and `analytic-geometry` prerequisites
do not apply. What it does need is the workspace convention: fix a divisible
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
  needed to read it.
- [`computer-algebra`](../../foundations-and-computation/computer-algebra/) is
  where the exact-operation contract of §11 belongs: which operations a
  symbolic scalar representation must supply for the scale algorithm to run,
  and why finite truncation cannot certify every exact rank.

## The gap claim, checked

The report claims that `docs/surcomplex/polynomial-algebra/` has Schur-type
arguments, differentiating compressions and Hermite signatures **but no
unified SVD, conditioning or singular-value scale theory**, and it states
that this is a coverage assessment rather than a claim that the repository
contains no matrices. Checked against the tree at commit `e260237`, **the
claim is accurate**, with one qualification.

- The three cited ingredients are really there. `polynomial-algebra`'s own
  README lists the sharp Schoenberg second-moment inequality "with the
  differentiating compression, an algebraic Schur inequality, and the
  collinearity equality case", and Hermite's signature criterion with the
  interval count `(sig T_1 + sig T_q)/2`.
- The claimed absence holds. Across all of `docs/`, *singular value*, *SVD*,
  *pseudoinverse* and *polar decomposition* occur outside this directory only
  in unrelated senses: `trigonometry`'s polar decomposition is the scalar
  `z = r·u` factorization, not the matrix one; `polynomial-algebra`'s
  "condition number" is a rootwise root-separation quantity; and
  `finite-deformations`' Gram matrices are residue pairings. No existing
  report proves a spectral theorem or an SVD over `F[i]`, and none develops
  matrix conditioning or a singular-value valuation theory.
- The qualification: the gap statement names `polynomial-algebra` as though
  it were the only place adjacent matrix material lives. It is not — Gram
  matrices in `finite-deformations` and Jordan/eigenvalue arguments in
  `differential-equations` are also nearby. This narrows the citation, not
  the gap; nothing in either report supplies what this one proves.

## What it does not claim

Every limitation the report shipped with is kept here.

- A rigorous integrated exposition with a non-Archimedean interpretation.
  **No priority claim**, and no claimed solution of a named open problem.
  Real-closed-field spectral theory, the SVD, low-rank approximation,
  pseudoinverses and classical perturbation theory are **not** presented as
  new; nor is priority claimed for the determinantal/valuation consequences.
  No exhaustive literature search is claimed.
- No infinite-dimensional operator theory: no Hilbert spaces over `No[i]`,
  bounded-operator spectra, compact or trace-class operators, spectral
  measures.
- No global analytic choice of eigenvectors through collisions or across
  multiple parameters. The pointwise spectral theorem alone does **not**
  yield a support-controlled Hahn expansion of an entire parameter-dependent
  eigenbasis.
- The exact decompositions do not by themselves give effective algorithms
  for arbitrary surreal inputs. `thm:series` is a strong-summability
  statement, not fine-topological convergence.
- All matrix dimensions are ordinary finite integers.
- The symbolic checks exercise the listed finite identities on their stated
  inputs. They do **not** machine-verify the general proofs, arbitrary Hahn
  supports, the proper-class foundations, or an effective representation of
  all surreal numbers. Exact symbolic zero tests are not replaced by
  truncation. None of the proofs has been formally verified. This is an
  AI-assisted draft, not refereed.
- The audit behind the article (`repository-audit.md`) inspected the
  catalogue, `polynomial-algebra`'s full inventory and the opening of its
  source, and the opening of the `foundations` README — not every archived
  source. A search returning no matches was not treated as proof that a
  topic occurs nowhere.

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
**30 pages**, 0 errors, 0 undefined references or citations, 0 LaTeX
warnings, 0 overfull and 0 underfull boxes; `data/build-report.json` records
the PDF inspection behind the delivered build.

The shipped `code/build.sh` and `code/build.ps1` both `cd` to their own
directory before invoking `latexmk article.tex`, and `article.tex` is in the
parent. They were written for the flat delivery layout and **do not work
from `code/`** — use the command above instead.

## Rerunning the finite checks

**Run these on a copy of the directory.** `code/verify-examples.py` defaults
its output directory to `../data`, so running it in place writes report files
into the directory that ships the recorded evidence. Copy the directory
elsewhere first, or redirect the output:

```sh
python -m pip install -r data/requirements.txt      # sympy==1.14.0
python code/verify-examples.py --output-dir "$TMPDIR/spectral-check"
```

Python 3.9 or newer. The matrix generator uses the fixed seed `20260921`;
no floating-point sampling is used anywhere.

What is recorded, and what has been rerun:

- `data/verification-report.json` and `.txt` are the delivered run:
  **176 exact assertions across 18 matrix-profile cases, PASS**, under
  Python 3.13.5 and SymPy 1.14.0. The article's appendix reports the same
  figures.
- The suite was **rerun for this collection and passed again — 176 exact
  assertions and 18 matrix-profile cases** — under Python 3.14.4 and SymPy
  1.14.0. The shipped JSON still records 3.13.5, because it is the delivered
  artifact and was deliberately not overwritten.

The valuation and elimination kernel is restricted to `Q(i)(t,u)`, with
`v(t) = (0,1)` and `v(u) = (1,0)` ordered lexicographically — so `u` is
smaller than every positive finite power of `t` in the corresponding Hahn
interpretation. The **least** polynomial monomial, not SymPy's default
leading monomial, determines the Hahn valuation. The two-by-two spectral
examples are checked separately with exact square-root expressions.

Two notes on the shipped layout. The script writes underscore filenames
(`verification_report.json`, `verification_report.txt`), while the delivered
evidence was renamed to hyphens on ingest to match the rest of the
collection — so a rerun in place would add files beside the recorded ones
rather than replace them, which is a further reason to run on a copy. And
the `MANIFEST.sha256` listed in the delivery note was not carried into the
repository; the file hashes are not reproduced here.
