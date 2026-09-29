# Nonreal Roots Survive in Polynomial Iterative Equations

**A cubic counterexample and a classification of circular spectra — Part II: the increasing spectral core on several circles**

This is a research report in two parts. Part I is the original report of
20 September 2026. Part II was added on 29 September 2026 in batch 41 of
ProveIt's incoming-report intake, from a later manuscript that classifies
what Part I left open: minimal iterative polynomials with roots on several
distinct circles, for increasing homeomorphisms of the real line. Both
sources were prepared for Vladimir Reshetnikov and are AI-assisted.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01 (original) | Cardinals-collection package *Nonreal Roots Survive in Polynomial Iterative Equations* (20 Sep 2026) | `nonreal_roots_research.zip` (as the collection manifest records it) | (none) | in ProveIt since `dc54c3cb3` | Part I: Sections 1–11 (pp. 4–20), Appendices A–B (pp. 40–41) |
| 02 | batch 41, manuscript 02 (*The Complete Increasing Spectral Core: Arbitrary-radius classification, optimal order reduction, and fixed-point spectra for polynomial iterative equations*, 28 Sep 2026, 20-page Letter PDF as delivered) | `ProveIt_Increasing_Spectral_Core.zip` (inner `Increasing_Spectral_Core/`, main file `article.tex`) | blob `ae6ea0aa` of Part I's `article.tex` | `eaf787d50` (prefix `02-spectral-core-`) | Part II: Sections 12–24 (pp. 21–39) |

Manuscript 02 is pinned by the Git blob
`ae6ea0aa0566316ba9ed06b1750c6e73275059da` of Part I's `article.tex`, which
its author retrieved through the GitHub content API on 28 September 2026, not
by a commit. That blob is the one committed in `dc54c3cb3` and was unchanged
at the placement commit, so every statement manuscript 02 makes about Part I
refers to the text printed here. The archive arrived in `9754e8360`; its
manuscript, PDF, delivery README and checksum ledger (`MANIFEST.sha256`,
11/11 verified at placement) are not shipped and survive in the arrival
commit. Part II prints every result, proof, example, remark, limitation and
question of the manuscript. What it reproves from Part I (homeomorphism
lemma, annihilator ideal, two-sided recurrence decomposition, orbitwise least
common multiples, simultaneous returns and positive means, the translation
argument for `(z−1)^2`) is printed once, in Part I, and credited in
Section 13.1 and at each use. Section 12.1 of the article lists where the
merge had to choose.

**Status.** AI-assisted and unrefereed. Nothing here is formalized in Lean,
Rocq or any other proof assistant, and neither source claims otherwise. The
finite computations check stated finite ranges and implementations; they are
not a proof of the universal statements. Neither part makes a priority claim.

## Results

For `P(z) = Σ a_j z^j`, `P[f]` means `Σ a_j f^{∘j}` (composition, not
pointwise powers); `μ_f` is the monic least-degree annihilator.

**Part I** (unchanged apart from a second subtitle line, a title-page
paragraph on Part II and dated pointers) answers Problem 6.1 of Draga and
Morawiec (*Aequationes Math.* 90 (2016), 935–950; arXiv:1503.00570v2, p. 13)
negatively: an odd increasing bi-Lipschitz homeomorphism `F` with
`F^{∘3}(x) = 8x`, `F(1) = 3` and `μ_F = z^3 − 8` (Theorem 2.1, Hankel
determinant −56), and a real-analytic map with `μ_f = (z−1)^2(z^2+1)`
(Theorem 3.1). It classifies the minimal polynomials of increasing
homeomorphisms with all roots on one circle `|z| = r` (Theorem 6.1): for
`r ≠ 1` the root `r` has odd multiplicity at least every other; at `r = 1`
either `μ = z − 1` or `1` has even multiplicity exceeding every other. It
also gives quantitative square-free realizations (Proposition 7.1), circular
rigidity criteria (Corollaries 8.1, 8.2) and fixed-point regularity results
(Theorems 9.1, 9.2 and a `C^1` counterexample).

**Part II** (manuscript 02) works with the *difference spectrum* `𝒟μ`, `μ`
with one copy of `z − 1` removed. It proves:

1. **Classification with arbitrary root moduli** (Theorem 12.2; manuscript
   Theorem 1.2). A nonconstant monic real `μ` with `μ(0) ≠ 0` is `μ_f` for an
   increasing homeomorphism of `R` iff `μ = z − 1` or `𝒟μ` is
   *positive-admissible*: on each extreme modulus circle the positive real
   root is present with maximal multiplicity on that circle, and it is odd if
   there is only one circle; interior circles are unrestricted. Every
   permitted spectrum is realized by a globally bi-Lipschitz map, real
   analytic except possibly at one fixed point (everywhere analytic and
   fixed-point-free when the extreme moduli of `𝒟μ` bracket 1). Example:
   `(z−2)^2(z−4)^2` is realizable, `(z−2)^2` and `(z−1)(z−2)^2` are not.
2. **The increasing spectral core** `ℛ(P) = (z−1)^{δ(P)} 𝒦(𝒟P)`
   (Definition 16.1, Theorem 16.3; manuscript Theorem 5.3): an explicit
   root-by-root divisor of `P` such that every continuous increasing solution
   of `P[f] = 0` satisfies `Q[f] = 0` iff `ℛ(P) | Q`, and one bi-Lipschitz map
   has minimal polynomial exactly `ℛ(P)`. Increasing solutions exist iff `P`
   has a positive real root. Worked example: degree 32 → 23 (Section 19.4).
3. **Rigidity** (Theorem 17.1; manuscript Theorem 6.1): all increasing
   solutions are affine iff `ℛ(P) = z − r` (`r > 0`) or `(z−1)^2`, and
   homogeneous linear iff `ℛ(P) = z − r`.
4. **Fixed points**: the fixed set is empty or a closed interval
   (Proposition 18.2); a fixed-point-free realization exists iff
   `r_− ≤ 1 ≤ r_+` for the extreme moduli of `𝒟μ` (Theorem 18.3; manuscript
   7.3); an exact criterion for realizations with a fixed point
   (Theorem 18.4; manuscript 7.4).
5. **Examples**: a rational polygonal map with `μ = (z−2)^2(z−4)^2` (Hankel
   determinant 16384/9), an everywhere analytic map with
   `μ = (z−½)(z−2)(z^2+1)` (Hankel 225/256), and, for every `m ≥ 1`, an
   analytic fixed-point-free map with `μ = (z−½)(z−2)(z^2+1)^m` and
   `1/6 ≤ f' ≤ 6` (Theorem 19.1; manuscript 8.1).
6. Ten research questions and a staged Lean plan (Section 21; none started).

Added in the merge (not stated by the manuscript): Remark 15.3 shows that on
one circle Theorem 12.2 is Part I's Theorem 6.1, and Remark 17.2 that
Theorem 17.1 gives Part I's Corollaries 8.1 and 8.2. As a finite check, the
manuscript's `realizable()` was compared in the write phase with the
conditions of Theorem 6.1 on **638 single-circle spectra** (radii 2 and 1;
roots `±r`, the pair `±ri` and the pair `r(3±4i)/5`; positive-root
multiplicity 0–4, the other three 0–3; empty spectrum excluded; 2 × 319):
**0 disagreements**. That comparison script is not shipped; the grid
specifies it.

## Not claimed

- No classification of decreasing solutions (Section 21, Q1, explains why a
  sign swap is not enough), of arbitrary proper-interval or one-sided domains,
  of noninjective equations with zero constant coefficient, or of all
  individual maps realizing an admissible spectrum. Petrov's unrestricted
  linearity question is not declared solved.
- No global complex analyticity, and no differentiability at the fixed point
  in the half-line case of Theorem 12.2 (Remark 15.2).
- No factorization of arbitrary polynomials by the shipped code: it accepts
  factored spectra with Gaussian-rational roots only.
- No claim that the finite grids (1,354 spectra, 97,281 divisors), recurrence
  windows or Hankel determinants certify the universal or analytic
  statements.
- No novelty for the conjugacy method (Part I), for the piecewise-linear
  non-affine map of Theorem 17.1 (Bogdanov's comment on Petrov's question),
  or for the classical recurrence framework. No priority: both literature
  checks were targeted (Part I on 20 September 2026, Part II on
  28 September 2026), not exhaustive; the research questions of Section 21
  are not claimed open throughout the literature.
- No referee report and no Lean or Rocq certification.

## Labels

Part I's 87 labels are bare (`sec:`, `eq:`, `thm:`, `lem:`, `prop:`, `cor:`,
`tab:`, `fig:`, `app:`) and are unchanged, with unchanged numbers (compared
in the `.aux` files of the committed and the new build; only their pages
moved, by one, because the contents now take two pages). Part II added
**69** labels, all with the prefix `nrr:sc:` ("nonreal roots, spectral
core"). Total: 156. No label was renamed or removed. Of the manuscript's 67
labels, 62 are printed with the prefix; the five whose content is printed
once in Part I (`lem:homeo`, `lem:expoly`, `eq:rightcomposition`, `eq:orbit`,
`eq:expoly`) are not; seven labels are new (`sec:source`, `sec:notation`,
`tab:notation`, `sec:imported`, `sec:conclusion`, `rem:circular`,
`rem:rigidity-recovers`, each with the prefix). Part II starts at Section 12;
its one numbered table continues Part I's numbering (Table 3) and its
equations continue Part I's (from (71)). Part I's appendices come after
Part II and contain no numbered equations, tables, figures or theorem-like
items. The manuscript's two appendices are printed as Sections 23–24.

## Notation

Part I's symbols keep their meanings. Table 3 (Section 12.2) lists Part II's
symbols with the tempting false readings; in particular:

- `𝒟A` removes **one** copy of `z − 1`, not the whole `(z−1)`-primary
  factor; it is not Part I's dilation `D_2`, `D_8` (Section 2.3).
- `ℛ(P)` is the core, not the real line; `𝒦(B)` the positive-recurrence core.
- `A` is a polynomial (a spectrum) in Part II, a polynomial *function* `A(t)`
  in Part I's constructions; `W`, `G`, `H`, `F`, `h` are local to their
  constructions (Part I's `F` is the cubic counterexample).
- Renamed from the manuscript: the large constant `T` of the envelope lemma
  → `Λ`; the least and greatest positive roots `a < b` in the annular core
  formula → `b_− < b_+` (the manuscript also uses `a < b` for logarithmic
  rates); the odd cap `k` → `κ` (Part I's `k` has `m_r = 2k + 1`); the glued
  fixed-point map `G` → `Φ`. No normalization changed.

## Files

```
article.tex                     the report, standalone LaTeX with an internal bibliography
article.pdf                     the compiled report, 42 Letter pages (title and abstract p. 1, contents pp. 2–3,
                                Part I pp. 4–20, Part II pp. 21–39, Part I's appendices pp. 40–41, references p. 42)
README.md                       this guide
Makefile                        Part I: verify, illustrations, pdf and clean targets (run in place; see below)
STATUS.md                       Part I: claims, computations and limits as delivered (stale in one line; see below)
manifest_entry.tex              Part I: the suggested catalogue entry delivered with it (describes Part I only)
requirements-optional.txt       Part I: matplotlib, needed only for `analytic_demo.py --plots`
02-spectral-core-STATUS.md      Part II: manuscript 02's status and claim boundaries (delivered as STATUS.md)
02-spectral-core-source_audit.md  Part II: manuscript 02's source record (delivered as notes/source_audit.md)
code/verify.py                  Part I: exact rational checker (two independent cubic implementations)
code/analytic_demo.py           Part I: floating-point illustration and optional plot generator
code/02-spectral-core-spectral_core.py  Part II: exact root-level core and classification routines
                                (delivered as code/spectral_core.py)
code/02-spectral-core-verify.py Part II: finite grid, recurrence and Hankel checks (delivered as code/verify.py)
code/02-spectral-core-example.py  Part II: the order-32 → 23 example (delivered as code/example.py)
data/exact_certificates.json    Part I: matrices, coefficients and results of code/verify.py
data/numerical_illustration.json  Part I: explicitly noncertifying floating-point results
data/selection.json             Part I: the random area draw and all 80 candidate areas
data/02-spectral-core-exact_checks.json  Part II: recorded verifier output (delivered as results/exact_checks.json)
data/02-spectral-core-verification.txt   Part II: its short log (delivered as results/verification.txt)
data/02-spectral-core-example.txt        Part II: recorded output of the example (delivered as results/example.txt)
figures/cubic_counterexample.pdf, figures/analytic_displacement.pdf   Part I: the two figures
notes/literature_audit.md       Part I: source identifiers, what was checked, search limits
notes/selection_and_exclusion.md  Part I: random-draw and manifest-exclusion record
```

The eight `02-spectral-core-` files were staged in the placement commit
`eaf787d50`, byte-identical to the delivery (re-verified in the write phase
against a fresh extraction). The manuscript's `article.tex`, `article.pdf`,
`README.md` and `MANIFEST.sha256` are not shipped.

## Build the article

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

or run `pdflatex article.tex` three times. Build in a scratch copy of
`article.tex` and `figures/`, so that no auxiliary files land here: Part I's
`make pdf` runs LaTeX in place. Needed packages: newtx, amsmath/amsthm/
mathtools, geometry, microtype, graphicx, booktabs, tabularx, enumitem,
fancyhdr, xurl, hyperref, listings, caption. No bibliography processor is
needed. The shipped PDF was built with MiKTeX (pdfTeX) with no errors, no
warnings, no undefined or multiply defined references, no duplicate
destinations and no overfull or underfull boxes (as was the committed Part I
text). The DejaVu Type 3 fonts in it come from Part I's two Matplotlib
figures.

## Rerun the checks

Python 3.9+ with the standard library suffices for both parts. Run normally,
not with `-O`: both verifiers use assertions.

**Part I.** `code/verify.py` writes `data/exact_certificates.json` by default
and `code/analytic_demo.py` rewrites `data/numerical_illustration.json` (and,
with `--plots`, the two figures) in place, so do not run them here. From this
directory:

```sh
W=/path/to/scratch
py code/verify.py --output "$W/exact_certificates.json"   # 4,026 rational points, 4,025 secant checks,
                                                          # 4 Hankel determinants (-56, 1, -512, degree 15)
mkdir -p "$W/01" && cp -r code data figures "$W/01/" && (cd "$W/01" && py code/analytic_demo.py)
```

`make verify` and `make illustrations` run the same scripts in place and
would overwrite the shipped records.

**Part II.** The shipped scripts cannot run under their shipped names:
`02-spectral-core-verify.py` and `02-spectral-core-example.py` do
`from spectral_core import …` and fail with `ModuleNotFoundError`, and the
verifier writes to `parents[1]/results/`, which would create a stray
`results/` directory here. Restore the delivered layout in a scratch copy
(Git Bash or another POSIX shell, from this directory):

```sh
W=/path/to/scratch
mkdir -p "$W/02/code"
for f in code/02-spectral-core-*.py; do cp "$f" "$W/02/code/${f#code/02-spectral-core-}"; done
cd "$W/02"
py code/verify.py                    # writes results/exact_checks.json, results/verification.txt
py code/example.py > example.txt     # the recorded data/02-spectral-core-example.txt
```

This was run on 29 September 2026 (Python 3.14.4, about 1 s): the verifier
passed (1,354 spectra, 97,281 divisors, recurrences on −80 ≤ n ≤ 80, 402
monotonicity assertions, Hankel determinants 16384/9 and 225/256, 32 → 23),
and both outputs and the example's output equal the shipped files apart from
Windows line endings. The article's Python snippet (Section 20.1) likewise
needs the delivered name `spectral_core` on the module path of such a copy.
The grid check in the verifier enumerates divisors independently of the core
formula, but uses the same `positive_admissible` routine as the module; the
638-spectrum comparison above checks that routine against Part I's
independently stated theorem.

## Discrepancies and delivery names

- **Stale delivered text.** Part I's `STATUS.md` lists "A classification when
  roots have different moduli" under "Not established here" (line 59). For
  increasing homeomorphisms of `R` it is now established in Part II. The file
  is kept byte-identical; the article's corresponding sentences (title page,
  Sections 1.2, 6, 8 and 11, the Petrov bibliography entry) carry dated
  pointers to Part II. `manifest_entry.tex` and `notes/literature_audit.md`
  also describe Part I only.
- **Unshipped files named in delivered text.** The delivery README of Part I
  listed `checksums.sha256`, which is not shipped (and this README replaces
  that delivery README). Part I's Appendix B names the user-supplied
  `manifest(1).tex`, which was never redistributed (its SHA-256 is recorded).
  Part II's scripts name `results/` and `spectral_core`; its source audit says
  "No source paper is repackaged in this archive" about the delivered archive.
- **Delivery layout in Part I's text.** Part I's Appendix B and `Makefile`
  run from "the archive's top-level directory" and build in place; use the
  scratch-copy commands above instead.
- **Page size.** Both parts are US Letter, as delivered.
- **Citations.** The manuscript cites arXiv:1503.00570 without a version and
  Petrov's MathOverflow question with I. Bogdanov's comments; Part II uses
  Part I's bibliography entries for the same works, and the Petrov entry
  gained a dated note about the comments. Part I's statement that the
  question "had no posted answer" concerns answers, not comments, and stands.

## Relation to neighbouring reports and to the formal project

No other report in the research-report collection treats polynomial
iterative equations, and manuscript 02 names no report other than Part I, so
no reciprocal note was written. The report sits in the `log-concavity-and-
unimodality` category of the research-report collection of the
`SetTheory/Cardinals` Lean project. That placement confers no formal status:
no Lean or Rocq declaration anywhere in ProveIt formalizes any statement of
Parts I–II. Section 21 (Q10) records the staged formalization plan
the manuscript proposes; none of it has been started.

## Sources and attribution

S. Draga and J. Morawiec, *Reducing the polynomial-like iterative equations
order and a generalized Zoltán Boros' problem*, Aequationes Mathematicae 90
(2016), 935–950, https://doi.org/10.1007/s00010-016-0420-4, arXiv:1503.00570
— Problem 6.1 (preprint p. 13).

S. Draga, *A note on the order of polynomial-like iterative equations*,
Commentationes Mathematicae 56 (2016), 243–249, arXiv:1604.01287v2.

F. Petrov, *Continuous linear recurrent relations*, MathOverflow question
232493 (1 March 2016), with comments by I. Bogdanov.

Part I also cites Draga–Morawiec, *Means of iterates* (arXiv:1801.05006v2),
and Thangroongvongthana–Laohakosol–Mavecha, *Current Applied Science and
Technology* 21(3) (2021), 495–523. No third-party paper PDFs are included.
