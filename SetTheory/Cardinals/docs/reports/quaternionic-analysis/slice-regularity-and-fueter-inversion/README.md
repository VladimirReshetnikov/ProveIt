# Slice regularity and the global inverse Fueter problem

**Affine monodromy, spherical residues, and the energy of a singular sphere —
with a self-contained account of slice-regular and Cauchy–Fueter analysis,
and polynomial periods in every even dimension**

One article assembled from **eleven separately delivered manuscripts**, with
the duplicated mathematics stated once. Ten were merged on 21 September 2026;
the eleventh was added on 28 September 2026 as Parts XII–XIII.
[`MERGE_NOTES.md`](MERGE_NOTES.md) records the provenance, the notation
reconciliation, the thirteen conflicts between the first ten sources, and a
dated section on the eleventh.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01–10 | delivered directly (no batch number) | the ten archives tabulated in `MERGE_NOTES.md` | none recorded (delivered before pinning) | merged in `1ef935074` (Cardinals history, 21 Sep 2026) | Parts 0–XI (§§1–13), Appendices A–E |
| 11 | batch 39, manuscript 01 | `ProveIt_Fueter_Polynomial_Periods.zip` (*Polynomial Periods and Sharp Residue Hierarchies for the Global Inverse Fueter Map*, 25-page PDF) | `fbba58593` | `e2b1f016a` | Parts XII–XIII (§§14–15), Appendices F–G |

These are AI-assisted research notes. **None of the eleven sources is
refereed, and nothing here is formalized** in Lean or Rocq; the merge does not
change that.

## What this is

The first ten are not ten topics. One of them — `quaternionic_analysis.zip`,
dated 20 September 2026 — is an expository survey, *Classical Complex
Theorems over the Quaternions*. The other **nine were all written on
21 September 2026 as independent attempts at the same follow-up problem**,
and one of them ships a verbatim copy of the survey as its `source_context/`.
The eleventh was written later, *from* this report (it inspected this README
at commit `fbba58593`, nothing else), and takes the theory to higher
dimensions.

So the article has three layers:

- **Part I** is the survey: slice regularity and Cauchy–Fueter regularity side
  by side, with Cauchy formulas, Taylor and Laurent expansions, maximum and
  minimum principles, the regular product and the geometry of zeros, the
  argument principle and Rouché, open mappings, Schwarz–Pick and an intrinsic
  Riemann mapping theorem.
- **Parts II–XI** are the global inverse Fueter problem in four dimensions:
  given an axially monogenic `g`, when is there a single-valued slice-regular
  `f` with `Δ₄f = g`?
- **Parts XII–XIII** (source 11) are the same problem for the Fueter–Sce map
  `Δ_{2h+2}^h` in every even ambient dimension `2h+2`, on product domains in
  the upper half-plane. They answer open problem (O4) of §13.4.

## The answer, in one display

For `g = P + IQ` axially monogenic on the circularization of a planar domain,
form the two closed quaternion-valued one-forms

    ω_g = ½(−P dx + Q dy)
    θ_g = ½((xP + yQ) dx + (yP − xQ) dy)

A single-valued slice-regular primitive exists **exactly when both have
vanishing periods**; then `f(x+Iy) = (x+Iy)C + V` with `dC = ω_g`, `dV = θ_g`,
unique up to `q ↦ qa + b`. The monodromy is affine, the period pair
`(a_γ, b_γ)` is a complete obstruction, and the cokernel of the Fueter map has
real dimension `8m` where `m` counts the holes.

The point that the nine manuscripts exist to make is that **θ_g is computed
from the target**, with no first primitive chosen. The original survey's local
construction integrates one form and then a second form that depends on the
first primitive; the substitution `V = A − xB/y` removes that dependence, and
`η_C − d(xC) = θ_g` is the identity that connects the two.

In dimension `2h+2` (source 11) the pair becomes **one polynomial-valued
closed form** of degree `2h−1` in a real formal variable `t`,

    ϖ_h[g](t) = λ_h ((t−x)² + y²)^(h−1) [ ((x−t)P + yQ) dx + (yP − (x−t)Q) dy ],
    λ_h = (−1)^(h+1) / (2^(2h−1) h! (h−1)!),

with `ϖ_1[g](t) = θ_g + t ω_g`. Its periods are a complete obstruction, the
inverse is recovered by integrating the coefficients and evaluating the
resulting polynomial at `t = z`, and the cokernel has real dimension
`2h·d_V·m` (`d_V` = dimension of the real Clifford module; `8m` at `h = 1`).

## Nine independent derivations agreeing is the evidence

All nine reach the same two forms, the same criterion, the same affine
monodromy, the same `8m`, and the same leading constant in the logarithmic
energy law. They were written separately and they agree. That is worth more
than any one of them. Source 11, rederiving its `h = 1` case independently,
reproduces the two forms, the criterion, the affine kernel, `8m`, the
axial-pair constant `R_p(a,b)/(πv)` and the energy coefficient `8R_p(a,b)²`
by different routes; the article marks each of these as a second route.

Where the first ten *disagree* it is almost always notation, and
`MERGE_NOTES.md` lists all thirteen cases. Two were mathematical and would
have produced a false statement if the merge had been mechanical:

- **The size law at a critical singularity** has two different sharp constants
  in two different norms — the supremum over the whole conjugacy sphere, and
  the axial pair norm — and four manuscripts used the same symbol `M_g` for
  both. At `p = ι, a = 1, b = i` the constants are `2/π` and `√2/π`. The
  article uses different symbols and states both laws. Source 11's sharp
  constants are all in the axial-pair norm and keep this distinction.
- **The conserved flux that recovers the slope residue** needs the weight
  `H_u = 3(Re q − u) + Im q`, not the naive `q − u`. The coefficient 3 is what
  makes the weight right-Fueter-regular: `Σ_μ ∂_μ(q−u)e_μ = −2`, whereas
  `Σ_μ ∂_μ H_u e_μ = 0`. A flux weighted by `q − u` is not conserved, so a
  merge that presented the moment formula as a computable flux would have been
  wrong.

Source 11 conflicts with none of the ten mathematically. It did collide in
notation with about twenty symbols (`m`, `b`, `d`, `D`, `E`, `J`, `Ω`, `κ`,
`C`, `H`, `R_t`, `r`, `s`, …); all are renamed in the article, Table 2
(§14.3) lists every renaming, and the false readings that remain tempting are
printed beside the true ones there.

## What source 11 adds (Parts XII–XIII)

Proved in the article, for every `h ≥ 1`, under the stated hypotheses
(smooth axial targets; connected planar domain strictly inside the upper
half-plane; the unnormalized `h`-th power of the Laplacian):

- closedness and injectivity of the current, and the **moving
  Hermite-polynomial identity** `dΘ_F(z;t) = ϖ_h[Δ^h I(F)](t)` (Theorem 14.9),
  proved by an exact finite-jet spanning argument, not by extrapolation from
  tested `h`;
- the polynomial kernel `P_{<2h}(V)` (classical; reproved), the complete
  constructive global inverse (Theorem 14.11), polynomial monodromy, the exact
  sequence with cokernel `2h·d_V·m` for bounded domains with `m+1` `C¹`
  Jordan boundary curves (Theorem 14.15), and the **smallest inverse cover**,
  with no finite cover possible when a period is nonzero (Theorem 14.16);
- at a punctured sphere `p = u + ιv`, the residue polynomial and the exact
  **residue filtration** `frak-R_N(p) = ((t−u)²+v²)^(h−N) · P_{<2N}(V)`, of
  dimension `2N·d_V` (Theorem 15.3), which has no nontrivial intermediate
  levels when `h = 1`;
- sharp, attained **axial-pair size constants** and **physical energy
  divergence constants** at every level (Theorems 15.5 and 15.8), and the
  classification of residue classes admitting local `L^α` representatives,
  `α ≥ 1` (Corollary 15.9);
- six-dimensional worked examples, ten research questions (Q1)–(Q10), and
  Appendices F–G (explicit Hermite interpolant; explicit radial coefficient
  formulas).

(O4) is re-scoped in place (§13.4) with a dated pointer; its original wording
is kept.

## What is not proved, and what is not claimed

From the first ten, both stated in the article where they arise:

- The attribution of the arctangent / spherical Cauchy kernels is **left
  open**. The manuscripts cite two different papers as the primary source and
  the question cannot be settled from the manuscripts themselves; both are
  cited and the article says so.
- An editorial dispute about whether a published surjectivity statement is
  being corrected is recorded, not adjudicated.

From source 11 (all kept in §14.2 and §15.8):

- Written proofs, **not** referee-validated and **not** Lean-verified.
  Historical priority was not established by its focused literature check;
  the Fueter–Sce mapping, local inverse formulas and the polynomial kernel
  are credited to existing theory. There is no claimed contradiction with
  published surjectivity results (Perotti's Theorem 2 assumes simply
  connected components); this matches the article's single editorial
  position.
- The code checks finite ranges only (closedness `h ≤ 8`, Hermite identity on
  60 real-monomial and 13 imaginary-monomial cases, periods `h ≤ 4`,
  asymptotics at the ten pairs `1 ≤ N ≤ h ≤ 4`); its numerical results are
  observed errors, not certified enclosures. No all-`h` statement rests on it.
- Out of scope for `h ≥ 2`: domains meeting the real axis (no analogue of
  Part V), nonaxial targets, fractional Fueter maps, growth-controlled
  realization with infinitely many holes, spherical-supremum constants, an
  exact energy law with a finite renormalized constant, surface sources and
  fluxes, and an `L¹` classification of germs. **Zero residue is not
  removability.** These limits are recorded as boundary item (B9) and in the
  re-scoped (O4).

## Relation to other work in the repository

This report has no neighbour in its category and continues no formal
development. No Lean or Rocq file in ProveIt concerns slice-regular,
Cauchy–Fueter or Fueter–Sce analysis, so **no statement of this report has a
formal counterpart**, and its placement in the `SetTheory/Cardinals` report
collection confers no formal status on it.

## Layout

```
article.tex                                     the merged article (pdfLaTeX, internal bibliography)
article.pdf                                     its build, 119 pages
README.md                                       this guide
MERGE_NOTES.md                                  provenance, notation table, the thirteen resolutions; dated section on source 11
build.sh                                        three pdflatex passes over article.tex, in place
11-polynomial-periods-PROOF_AUDIT.md            source 11's internal proof audit, as delivered
sources/01-primitives-spherical-residues.tex    the eleven manuscripts verbatim (.tex) with their
sources/01-primitives-spherical-residues-README.md   delivery READMEs (-README.md)
sources/02-inversion-topological-splitting.tex
sources/02-inversion-topological-splitting-README.md
sources/03-expository-survey.tex
sources/03-expository-survey-README.md
sources/04-affine-monodromy-range.tex
sources/04-affine-monodromy-range-README.md
sources/05-monodromy-spherical-residues.tex
sources/05-monodromy-spherical-residues-README.md
sources/06-mittag-leffler-realization.tex
sources/06-mittag-leffler-realization-README.md
sources/07-defects-energy-laws.tex
sources/07-defects-energy-laws-README.md
sources/08-reflection-residue-energy.tex
sources/08-reflection-residue-energy-README.md
sources/09-monodromy-principal-parts.tex
sources/09-monodromy-principal-parts-README.md
sources/10-periods-integrable-singularities.tex
sources/10-periods-integrable-singularities-README.md
sources/11-polynomial-periods.tex
sources/11-polynomial-periods-README.md
code/01-primitives-spherical-residues.py        the ten verification programs of sources 01–10
code/02-inversion-topological-splitting.py
code/03-expository-survey.py
code/04-affine-monodromy-range.py
code/05-monodromy-spherical-residues.py
code/06-mittag-leffler-realization.py
code/07-defects-energy-laws.py                  (does not run as shipped; see below)
code/08-reflection-residue-energy.py
code/09-monodromy-principal-parts.py
code/10-periods-integrable-singularities.py
code/11-polynomial-periods-verify.py            source 11's exact symbolic and numerical checks (SymPy, mpmath)
code/11-polynomial-periods-build.sh             source 11's three-pass build of its own article (inert here; see below)
data/01-primitives-spherical-residues-verification_output.txt
data/02-inversion-topological-splitting-requirements.txt
data/02-inversion-topological-splitting-verification_results.json
data/03-expository-survey-verification.txt
data/04-affine-monodromy-range-requirements.txt
data/04-affine-monodromy-range-verification_results.json
data/05-monodromy-spherical-residues-requirements.txt
data/05-monodromy-spherical-residues-verification_output.txt
data/05-monodromy-spherical-residues-verification_results.json
data/06-mittag-leffler-realization-verification.txt
data/07-defects-energy-laws-requirements.txt
data/07-defects-energy-laws-source_and_pole_results.json
data/07-defects-energy-laws-validation.json
data/07-defects-energy-laws-verification_results.json
data/08-reflection-residue-energy-requirements.txt
data/08-reflection-residue-energy-verification.txt
data/09-monodromy-principal-parts-verification.txt
data/10-periods-integrable-singularities-verification_results.json
data/10-periods-integrable-singularities-verification_results.txt
data/11-polynomial-periods-requirements.txt     sympy==1.14.0, mpmath==1.3.0
data/11-polynomial-periods-verification.json    source 11's recorded run (PASS)
data/11-polynomial-periods-verification.log     its readable console log
```

Nothing was discarded: the deduplication is in the article. Every delivered
code, data, audit and source file is byte-identical to its delivery.

## Labels

The labels carry per-part prefixes: `a:` (Parts 0–I), `b:` (II–III), `c:`
(IV–V), `d:` (VI–VII), `e:` (VIII–IX), `f:` (X–XI and Appendices A–E), and
**`g:`** (Parts XII–XIII and Appendices F–G, added 2026-09-28). The merge of
source 11 added 118 labels, all `g:` (462 → 580); no label was renamed or
removed, and no earlier section, theorem or equation number changed (the new
parts follow §13 and the new appendices follow Appendix E).

## Building

Build on a copy, so that no auxiliary files land in the repository:

```sh
tmp=$(mktemp -d) && cp article.tex "$tmp" && (cd "$tmp" && latexmk -pdf article.tex)
```

`build.sh` does the same with three `pdflatex` passes but writes its `.aux`,
`.log`, `.out` and `.toc` files next to `article.tex`. The 28 September build:
119 pages, no errors, no undefined references or citations, no
multiply-defined labels, no duplicate PDF destinations.

## Running the verifiers

Run them on a copy of `code/` and `data/`: several write output files next
to themselves or into the working directory, and source 11's program
overwrites `data/verification.json` relative to its own location.

```sh
tmp=$(mktemp -d) && cp -r code data "$tmp" && cd "$tmp"
pip install sympy==1.14.0 mpmath==1.3.0 numpy scipy
for f in code/0*.py code/10-*.py; do python "$f"; done
python code/11-polynomial-periods-verify.py          # writes data/verification.json in the copy
```

Compare the copy's `data/verification.json` with
`data/11-polynomial-periods-verification.json`; on 28 September 2026 they
were identical apart from `elapsed_seconds`. The checks cover the
differential identities, the period formulas, the mode normalizations, the
residue-energy constants and the flux weights, and for source 11 the
Hermite identity, closedness, calibrations, periods and sharp asymptotics.
They do not replace the proofs, and each says so in its own output.

## Discrepancies and disclosures

- **`code/07-defects-energy-laws.py` does not run from the shipped files.**
  It does `from verify import paired_kernel`, a helper module from source
  07's delivery that was not kept in the 21 September merge; it stops with
  `ModuleNotFoundError`. Its recorded outputs in `data/07-*` remain the
  evidence. The other nine scripts of sources 01–10 and source 11's program
  ran and passed on a copy on 28 September 2026. (The original merge note
  that "all ten were run and all ten pass" refers to the delivered layout.)
- **Stray outputs.** Scripts 02 and 07 write `verification_results.json` /
  `source_and_pole_results.json` into the working directory, scripts 04, 05
  and 10 write `verification_results.json` (and 10 also
  `verification_results.txt`) into `code/`, overwriting one another, and
  source 11's program writes `data/verification.json`. Hence the copy.
- **Source 11's delivered texts use delivery names.** Its manuscript
  (`sources/11-polynomial-periods.tex`, Appendix "Reproduction and package
  contents" and §13) and README name `article.tex`, `article.pdf`,
  `code/verify.py`, `data/verification.json`, `data/verification.log`,
  `PROOF_AUDIT.md`, `requirements.txt` and `build.sh`; they are shipped as
  `code/11-polynomial-periods-verify.py`,
  `data/11-polynomial-periods-verification.{json,log}`,
  `11-polynomial-periods-PROOF_AUDIT.md`,
  `data/11-polynomial-periods-requirements.txt` and
  `code/11-polynomial-periods-build.sh`. Its `article.tex` is shipped as
  `sources/11-polynomial-periods.tex`; its `article.pdf` is **not shipped**.
  The article restates the reproduction appendix with the shipped names
  (§15.8).
- `code/11-polynomial-periods-build.sh` does `cd "$(dirname "$0")"` and builds
  `article.tex` there, which does not exist in `code/`; it is inert as
  shipped. To build source 11 on its own, copy
  `sources/11-polynomial-periods.tex` to a scratch directory as `article.tex`.
- `data/11-polynomial-periods-verification.log` ends with the delivery path
  `Saved /mnt/data/fueter_periods/data/verification.json`, and its elapsed
  time (7.7 s) is that of the delivered run.
- Source 11's numbering (its Theorems 5.2, 6.1, 7.3, 7.4, 9.3, 10.2, 11.2,
  Corollary 11.3, Sections 12 and 14, cited in its README) is its own; here
  they are Theorems 14.9, 14.11, 14.15, 14.16, 15.3, 15.5, 15.8,
  Corollary 15.9, §15.7 and §15.9.
- Source 11 writes `m = 2h+1` for the spatial dimension, `b` for holes, `E`
  and `d` for the coefficient module and its dimension, and `s` for the growth
  level; the article writes `2h+1`, `m`, `V` and `d_V`, and `N` (Table 2).
- **Pre-existing miscount, corrected in the article.** The reference list has
  26 entries, but two of them (Perotti, CMFT 24 (2024)) are the same paper,
  so it names 25 distinct works, not the 26 stated in `MERGE_NOTES.md` and in
  the original merge commit. The article's References preamble carries a
  dated correction.
