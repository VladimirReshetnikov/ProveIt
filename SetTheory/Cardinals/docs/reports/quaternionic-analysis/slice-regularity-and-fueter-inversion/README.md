# Slice regularity and the global inverse Fueter problem

**Affine monodromy, spherical residues, and the energy of a singular sphere —
with a self-contained account of slice-regular and Cauchy–Fueter analysis,
and polynomial periods in every even dimension, across the real axis and on
infinitely connected domains**

One article assembled from **twelve separately delivered manuscripts**, with
the duplicated mathematics stated once. Ten were merged on 21 September 2026;
the eleventh was added on 28 September 2026 as Parts XII–XIII, and the twelfth
on 30 September 2026 as Part XIV.
[`MERGE_NOTES.md`](MERGE_NOTES.md) records the provenance, the notation
reconciliation, the thirteen conflicts between the first ten sources, and a
dated section on the eleventh. The twelfth's provenance, choices and
renamings are recorded in the article (§16.1 and Table 3) and in this README;
`MERGE_NOTES.md` was not extended for it.

| Source | Manuscript | Archive | Pin | Placed | Printed as |
|---|---|---|---|---|---|
| 01–10 | delivered directly (no batch number) | the ten archives tabulated in `MERGE_NOTES.md` | none recorded (delivered before pinning) | merged in `1ef935074` (Cardinals history, 21 Sep 2026) | Parts 0–XI (§§1–13), Appendices A–E |
| 11 | batch 39, manuscript 01 | `ProveIt_Fueter_Polynomial_Periods.zip` (*Polynomial Periods and Sharp Residue Hierarchies for the Global Inverse Fueter Map*, 25-page PDF) | `fbba58593` | `e2b1f016a` | Parts XII–XIII (§§14–15), Appendices F–G |
| 12 | batch 64, manuscript 03 | `ProveIt_Fueter_Global_Inversion.zip` (*Global Fueter Inversion Beyond Finite Connectivity*, 26-page PDF, dated 30 September 2026) | `cb1646dc4` | `3025c15df` | Part XIV (§16) |

These are AI-assisted research notes. **None of the twelve sources is
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
dimensions. The twelfth was written from the report too (it inspected this
README and source 11's manuscript at commit `cb1646dc4`), and continues the
eleventh.

So the article has three layers, the last in two stages:

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
- **Part XIV** (source 12) carries that problem across the real axis, onto
  conjugation-symmetric domains, and to planar domains of arbitrary (also
  infinite) connectivity, and classifies when the realization of periods can
  be chosen continuously and linearly. It answers question (Q1) of §15.9 and
  parts of (Q4), (Q5) and open problem (O2).

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

Across the real axis (source 12) nothing new is needed: on a
conjugation-symmetric domain the Hermite primitive of an intrinsic stem becomes
the Taylor polynomial of order `2h−1` on the axis, the same criterion holds,
and a conjugation-fixed hole contributes nothing while each conjugate pair
contributes `2h·d_V`. On an arbitrary planar domain every admissible period
character occurs, and realizing arbitrary periods by a continuous linear
choice is possible **exactly when the admissible period rank is finite**.

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

Source 12 conflicts with none of the eleven mathematically either. At `h = 1`
it reproves Part V's real-axis criterion (Theorem 6.3) and its count `8m`
(Theorem 6.8) by different routes (a confluent contour formula; Cousin
theory), and the article marks both as second routes. It wrote in its own
notation (`\Fu`, `E`, `d`, `κ_h`, `C_h`, `c(z)`, `p`, `q`, `r`, `ρ`, `R`,
`T`, `V`, `A_{j,k}`, `Φ_j`, `b_j`, …), which collides with about forty symbols
of the article; all are rewritten, Table 3 (§16.3) lists every renaming, and
the three tempting false readings (admissible rank is not the number of holes;
inversion is not realization; the period space is a product, not a direct sum)
are printed there. In particular source 12's single-letter Fueter map `\Fu`
does not survive: the article's rule that the Fueter map is never one letter
is kept.

## What source 12 adds (Part XIV)

Proved in the article, for every `h ≥ 1` and every nonzero real Clifford
module, under the stated hypotheses (smooth axial targets, with even/odd
parity and smoothness through the axis on symmetric domains; connected planar
domains; the unnormalized `h`-th power of the Laplacian):

- **regular confluence**: on a conjugation-symmetric domain the Hermite
  polynomial of an intrinsic stem extends real-analytically across the axis
  and equals the Taylor polynomial of order `2h−1` there (Theorem 16.6); the
  complete inverse criterion on both domain types, with all inverses
  (Theorem 16.8), and the kernel and normalization (`2h` real jet conditions
  at a real base point, Corollary 16.9);
- **every admissible polynomial period character is realized** on an
  arbitrary connected planar domain, with no finiteness or boundary hypothesis
  (Theorem 16.10), by de Rham and additive Cousin theory with reflection
  averaging; on a symmetric domain with `m` conjugate pairs and `s` fixed
  holes the cokernel has dimension `2h·d_V·m`, independent of `s`
  (Theorem 16.12); the examples `C∖{0}`, a real annulus, `C∖{±ι}`, `C∖Z`
  (infinitely many holes, admissible rank 0) and `C∖{2^j ± ι}` (rank ∞);
- the period space carries the quotient topology (Proposition 16.14), and the
  normalized inverse on zero-period targets is continuous and linear, with
  compact-set estimates that do not divide by the distance to the axis
  (Theorem 16.15);
- the **splitting dichotomy**: a continuous linear, or continuous positively
  homogeneous, right inverse of the period map exists exactly when the
  admissible period rank is finite, and at infinite rank no section has a
  continuous linear derivative anywhere (Lemma 16.16, Theorem 16.17,
  Corollary 16.18); nevertheless there is a **continuous nonlinear section**
  (Theorem 16.20), a nonlinear topological splitting (Corollary 16.21), and a
  **continuous linear section on every prescribed magnitude envelope**
  (Theorem 16.22);
- a six-dimensional confluent example, a three-loop period check, a
  dependency audit, eight research questions (R1)–(R8), and an audit of the
  hypotheses that cannot be dropped (§16.16).

The radial formula, the calibrations, the current and the Hermite identity,
which source 12 rederived, are the statements of Part XII; §16.6 restates them
under source 12's labels and prints only what is new (smoothness and
closedness through the axis, reflection invariance of the current, and the
constant `(−1)^h (2h)! I a / y^{2h}` of the central-imaginary stem for every
`h`).

Answered or re-scoped in place, with dated notes and the original wording
kept: (Q1) is answered; (Q4), (Q5) and (O2) are partly answered; (O4)'s "still
open" list, boundary items (B4) and (B9), the paragraph after Theorem 14.15,
§15.8's list of limits, the theorem audit (new rows and one amended cell), and
Part II's non-assertion of surjectivity for arbitrary `U` (before §3.6) now
point to Part XIV. The contribution ledger (§13.1), the literature boundary
(§13.2), the status paragraph (§1.2) and the reference-list preamble gain
dated sentences.

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
  re-scoped (O4). *(Corrected 2026-09-30: domains meeting the real axis are
  now treated for every `h` by Part XIV, and realization with infinitely many
  holes is proved there without growth control, in the unrestricted,
  nonlinear and fixed-envelope forms listed above; growth-controlled
  realization in the sense of sharp norm or growth bounds is still open. The
  other limits stand.)*

From source 12 (all kept in §16.2, §16.13, §16.16 and the remarks of §16):

- Written proofs, **not** refereed and **not** Lean- or Rocq-verified;
  historical priority not established by its focused literature check. The
  forward Fueter–Sce theorem and the polynomial kernel are classical, the
  current and Hermite identity are source 11's, de Rham, Cousin and open
  mapping theory are standard inputs, and the nonsplitting mechanism is
  classical Eidelheit theory (Vogt; Debrouwere–Vindas); source 12 claims no new
  abstract nonsplitting theorem.
- No characterization of period images in Hardy, Bergman, physical `L^p`,
  boundary-Hölder or Sobolev spaces; no sharp constants under degeneration of
  the domain; no sharp growth conditions near accumulating boundary
  components.
- The coordinate lifts behind the nonlinear and envelope sections exist by the
  open mapping theorem; **no effective algorithm and no explicit constants**
  are supplied for them. One linear section for all envelopes is impossible.
- The code is a finite diagnostic: exact checks for `h ≤ 8` (current) and
  `h ≤ 5` (monomials), 49 reflection matrices, and nine contour integrals whose
  largest observed error, below `2.7e−49`, is an observation, not a certified
  quadrature enclosure. It checks no Cousin solvability, no homology
  character, no infinite sum.
- The compact-set estimate is not a bounded operator between global function
  spaces; the constants depend on the domain, the base point and the path
  family.

## Relation to other work in the repository

This report has no neighbour in its category and continues no formal
development. No Lean or Rocq file in ProveIt concerns slice-regular,
Cauchy–Fueter or Fueter–Sce analysis, so **no statement of this report has a
formal counterpart**, and its placement in the `SetTheory/Cardinals` report
collection confers no formal status on it. This holds for Part XIV as well
(checked 2026-09-30): no `.lean` or `.v` file concerns Fueter maps, and
source 12 ships and relies on no formal proof. Its staged formalization plan,
question (R8), is a proposal (it sharpens (Q10)).

Within the report, Part XIV continues Part XII (source 11) directly, and at
`h = 1` it meets Parts II, V, VI and IX: the real-axis criterion and the `8m`
count of Part V (Theorems 6.3 and 6.8) are reproved by different routes,
the normalized inverse of Part VI (Theorem 7.8) is extended across the axis,
the closed range of Part VI (Corollary 7.6) becomes an open quotient map, its
finite-case continuous splitting (Corollary 7.7) is shown to fail at infinite
admissible rank, and the period content of the Mittag-Leffler realization of
Part IX (Theorem 10.3) loses its simple-connectivity hypothesis.

## Layout

```
article.tex                                     the merged article (pdfLaTeX, internal bibliography)
article.pdf                                     its build, 145 pages
README.md                                       this guide
MERGE_NOTES.md                                  provenance, notation table, the thirteen resolutions; dated section on source 11
build.sh                                        three pdflatex passes over article.tex, in place
11-polynomial-periods-PROOF_AUDIT.md            source 11's internal proof audit, as delivered
12-global-fueter-inversion-PROOF_AUDIT.md       source 12's internal proof audit, as delivered
12-global-fueter-inversion-PROVENANCE.md        source 12's repository and literature provenance notes, as delivered
sources/01-primitives-spherical-residues.tex    the twelve manuscripts verbatim (.tex) with their
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
sources/12-global-fueter-inversion.tex
sources/12-global-fueter-inversion-README.md
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
code/12-global-fueter-inversion-verify.py       source 12's exact symbolic and numerical checks (SymPy, mpmath)
code/12-global-fueter-inversion-build.sh        source 12's three-pass build of its own article (inert here; see below)
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
data/12-global-fueter-inversion-build_check.json      source 12's record of its own PDF build (26 pages), as delivered
data/12-global-fueter-inversion-requirements.txt      sympy==1.14.0, mpmath==1.3.0
data/12-global-fueter-inversion-verification.json     source 12's recorded run (PASS)
data/12-global-fueter-inversion-verification.log      byte-identical copy of the same JSON (see below)
```

Nothing was discarded: the deduplication is in the article. Every delivered
code, data, audit and source file is byte-identical to its delivery.

## Labels

The labels carry per-part prefixes: `a:` (Parts 0–I), `b:` (II–III), `c:`
(IV–V), `d:` (VI–VII), `e:` (VIII–IX), `f:` (X–XI and Appendices A–E),
**`g:`** (Parts XII–XIII and Appendices F–G, added 2026-09-28), and **`h:`**
(Part XIV, added 2026-09-30). The merge of source 11 added 118 labels, all
`g:` (462 → 580); the merge of source 12 added 92, all `h:` (580 → 672): its
84 labels with the prefix (for example `thm:split` → `h:thm:split`) and eight
new ones. No label was renamed or removed, and no earlier section, theorem,
equation, table or reference number changed (Part XIV is §16, after §15, and
the appendices still follow it as A–G; the four new references are appended
as [27]–[30]).

## Building

Build on a copy, so that no auxiliary files land in the repository:

```sh
tmp=$(mktemp -d) && cp article.tex "$tmp" && (cd "$tmp" && latexmk -pdf article.tex)
```

`build.sh` does the same with three `pdflatex` passes but writes its `.aux`,
`.log`, `.out` and `.toc` files next to `article.tex`. The 28 September build:
119 pages, no errors, no undefined references or citations, no
multiply-defined labels, no duplicate PDF destinations. The 30 September
build (with Part XIV): 145 pages, and again no errors, no undefined
references or citations, no multiply-defined labels and no duplicate
destinations; the four overfull boxes are those of the 28 September build,
and of the 33 underfull-box warnings (27 before) the six new ones are in the
narrow columns of the theorem audit's new rows, like its earlier rows.

## Running the verifiers

Run them on a copy of `code/` and `data/`: several write output files next
to themselves or into the working directory, and the programs of sources 11
and 12 both write `data/verification.json` relative to their own location, so
run in place they would drop an unprefixed stray file into `data/` and, run
one after the other, overwrite each other's output.

```sh
tmp=$(mktemp -d) && cp -r code data "$tmp" && cd "$tmp"
pip install sympy==1.14.0 mpmath==1.3.0 numpy scipy
for f in code/0*.py code/10-*.py; do python "$f"; done
python code/11-polynomial-periods-verify.py          # writes data/verification.json in the copy
python code/12-global-fueter-inversion-verify.py --output data/12-rerun.json
```

Compare the copy's `data/verification.json` with
`data/11-polynomial-periods-verification.json`; on 28 September 2026 they
were identical apart from `elapsed_seconds`. The checks cover the
differential identities, the period formulas, the mode normalizations, the
residue-energy constants and the flux weights, and for source 11 the
Hermite identity, closedness, calibrations, periods and sharp asymptotics.
They do not replace the proofs, and each says so in its own output.

Source 12's program takes `--output`, so its result can be given its own
name, as above; it also accepts `--skip-numerical` and `--max-h N`
(`1 ≤ N ≤ 8`; default 5, the recorded run). Compare `data/12-rerun.json` with
`data/12-global-fueter-inversion-verification.json`: on 30 September 2026
(Python 3.13.5, SymPy 1.14.0, mpmath 1.3.0, on a copy) they were identical
apart from `runtime_seconds` (9.0 s against the recorded 3.8 s) and line
endings — on Windows the program writes CRLF (`Path.write_text` in text
mode), while the shipped file has LF, so compare with line endings
normalized. Its checks cover the current (closedness, normalization,
reflection invariance, injectivity, the central-imaginary constant) through
`h = 8`, the Hermite identity and real-axis confluence on 55 monomial cases
each, 40 calibration monomials, 49 reflection matrices, and nine contour
periods at 60 digits; they do not check any global, topological or
infinite-dimensional statement.

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
  source 11's program writes `data/verification.json`, as does source 12's
  unless given `--output`. Hence the copy.
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
- **Source 12's delivered texts use delivery names.** Its manuscript
  (`sources/12-global-fueter-inversion.tex`, Appendix B "Reproducing the
  artifact" and §10.3) and its README name `article.tex`, `article.pdf`,
  `README.md`, `PROOF_AUDIT.md`, `PROVENANCE.md`, `build.sh`,
  `code/verify.py`, `code/requirements.txt`, `data/verification.json`,
  `data/verification.log` and `data/build_check.json` (its `PROOF_AUDIT.md`
  and `PROVENANCE.md` speak only of "the article" and "this package"); they
  are shipped as
  `sources/12-global-fueter-inversion.tex`,
  `sources/12-global-fueter-inversion-README.md`, the two root files just
  named, `code/12-global-fueter-inversion-build.sh`,
  `code/12-global-fueter-inversion-verify.py`, and
  `data/12-global-fueter-inversion-{requirements.txt,verification.json,verification.log,build_check.json}`.
  Its `article.pdf` (26 pages) is **not shipped**. The article restates the
  reproduction appendix with the shipped names (§16.13).
- `code/12-global-fueter-inversion-build.sh` likewise does
  `cd "$(dirname "$0")"`, builds `article.tex` there into a `build/`
  directory and copies `article.pdf` back; there is no `article.tex` in
  `code/`, so it is inert as shipped (and, pointed at a copy of the
  manuscript, it would write `build/` and `article.pdf` next to itself). To
  build source 12 on its own, copy `sources/12-global-fueter-inversion.tex`
  to a scratch directory as `article.tex` and run `pdflatex` three times.
- `data/12-global-fueter-inversion-verification.log` is **byte-identical** to
  `data/12-global-fueter-inversion-verification.json`: the delivered "log" is
  the program's standard output, which prints the same JSON it saves. Its
  `runtime_seconds` (3.837) and Python version (3.13.5) are those of the
  delivered run. `data/12-global-fueter-inversion-build_check.json` describes
  the build of source 12's own 26-page PDF, not of this report.
- Source 12's numbering (its Theorems 4.1, 4.3, 5.1, 6.1, 7.3, 8.2, 9.2 and
  9.4, Section 12 and Appendix A, cited in its README) is its own; here they
  are Theorems 16.6, 16.8, 16.10, 16.12, 16.15, 16.17, 16.20 and 16.22,
  §16.15 and §16.16. Its questions are (R1)–(R8); the ones its §§1 and 11
  and its `PROVENANCE.md` call "questions 1, 4 and 5" of source 11 are (Q1),
  (Q4) and (Q5) here.
- Source 12's notation is rewritten throughout (Table 3). In particular it
  writes `\Fu` (`F_h`) for the Fueter map, `E`, `d`, `J_j` for the module,
  `κ_h`, `C_h` for the constants, `c(z)` for the reflection, `p`, `q` for the
  numbers of conjugate pairs and fixed holes and `r` for the admissible rank;
  the article writes `Δ^h_{2h+2} I(F)`, `V`, `d_V`, `e_j`, `λ_h`,
  `(−1)^h c_h²`, `τ`, `m`, `s` and `r_adm`.
- **Wording not carried over.** Source 12's title page, PDF metadata and
  delivery README describe it as prepared for a named recipient, and its
  `PROVENANCE.md` says it was prepared "for the present request". The
  verbatim files keep that wording; the article records the manuscript only
  as an AI-assisted research manuscript in its provenance (§16.1).
- **A loose constant, kept.** In the proof of source 12's stable-inverse
  estimate (Theorem 16.15) the bracket of the current at `t = z` is bounded
  by `6R`; `3R` already suffices. The article keeps `6R` as printed and says
  so; only finiteness is used.
- **Bibliography.** Source 12's four new references (Forster; Prezelj–Vlacci;
  Vogt; Debrouwere–Vindas) are appended to the list as [27]–[30], as
  delivered and not rechecked against the publications. The list now has 30
  entries naming 29 distinct works (the Perotti duplicate below remains).
- **MERGE_NOTES.md** has no section on source 12: its provenance, the choices
  of the merge and its renamings are in §16.1–§16.3 of the article and in this
  README.
- **Pre-existing miscount, corrected in the article.** The reference list has
  26 entries, but two of them (Perotti, CMFT 24 (2024)) are the same paper,
  so it names 25 distinct works, not the 26 stated in `MERGE_NOTES.md` and in
  the original merge commit. The article's References preamble carries a
  dated correction.
