# Rank-One Non-Archimedean Analytic Geometry inside the Surcomplex Numbers

**Tate algebras, Berkovich disks, analytic annuli, and an entire-function
case study**

One standalone research article, `article.tex` (30 pages compiled), with
`code/` and `data/` holding the exact finite checks and their recorded
output. Not a merge: it has no `sources/`.

## What the report is

It works in a **fixed rank-one workspace**

    K = C((t^R)),   t^gamma = omega^(-gamma)  (Conway's monomial map),
    |a|_v = exp(-v(a))                        (a real-valued absolute value)

and asks what non-Archimedean analytic geometry over `K` actually looks
like. Because the value group is `R` and `K` is spherically complete, the
absolute value is a genuine one: `K` is a complete, algebraically closed
valued field (Poonen's Corollary 4), so it is a legitimate base for Tate
algebras and Berkovich spaces. This is the one place in the collection where
**convergence is real convergence**, not a Hahn identity — and the article
is careful to say that this is a property of the workspace, not of `No[i]`
(see *Where it sits*, below).

Four things are established over that field.

**A strict ring chain.** With `T = K<Z>` the unit-disk Tate algebra,
`P = C[Z]((t^R))`, `A = C{Z}((t^R))`, `F = C[[Z]]((t^R))` and `E^-` the
open-unit-disk analytic ring,

    K[Z] ⊊ T ⊊ P ⊊ A ⊊ F ⊊ E^-

with **every inclusion strict and an explicit witness for each** (Theorem
`thm:chain`; witnesses `Σ t^n Z^n`, `Σ t^(1−1/(n+1)) Z^n`, `Σ Z^n/n!`,
`Σ n! Z^n`, `Σ t^(−√n) Z^n`). The headline consequence is stated bluntly in
the article: `C[Z]((t^R))` is **not** the Tate algebra, although both can be
described informally as "series with polynomial coefficient data". A common
well-ordered Hahn support and a Gauss-norm tail tending to zero are
different conditions. The repository's common-domain rings `H(D) = O(D)((t^R))`
and `R_1 = colim H(D)` are located in the same chain, and a positive
monomial rescaling map makes the bridge operational rather than merely
descriptive.

**Zero geometry for convergent infinite series.** A constructive one-variable
Weierstrass preparation theorem (division as an actual Banach contraction,
not a formal slogan), principal ideals, finite quotient algebras, disk/shell/
residue-direction root counts, a valuation Rouché theorem, and the lift of a
simple residual root to an actual analytic root. This is the infinite-series
continuation of what `polynomial-algebra` proves in finite degree.

**Berkovich disks and annuli.** The relevant seminorm points are
constructed, together with the annulus deformation retraction onto its
interval skeleton, the Newton profile as a function on a radial segment, and
a product/Jensen formula on a disk. The sharpest lesson is a deliberate
mismatch: the Berkovich annulus is **contractible**, yet its analytic
de Rham class is **nonzero** — the residue is the complete obstruction to a
primitive. Ordinary complex topological intuition does not survive the trip
unless the differential-form category is checked first. Actual, annular and
cluster residues are kept apart.

**The case study.** `F(Z) = Σ_{n≥0} t^(n^2) Z^n`, worked out completely:
one simple zero of valuation `−(2m−1)` for each `m ≥ 1`, all zeros real and
negative, the first correction of the `m`-th normalized root occurring at
`t^(m(m+1))`, derivative valuations, a convergent canonical product with no
exponential correction factors, coefficient identities, and exact truncation
certificates. The series is `Θ_0(tZ, t^2)`, a rescaled classical partial
theta function; the article states plainly that it introduces neither the
series nor its leading root.

## Where it sits among the existing reports

Read the ring table in [`analytic-geometry`](../analytic-geometry/) first;
this article's chain is that table extended. Then note four relationships.

- [`analysis`](../analysis/) establishes that **there is no topological
  convergence anywhere in this theory**: every set of surcomplex numbers is
  closed and discrete in the fine topology. This article does not contradict
  that. Its convergence is in the *intrinsic valuation topology of the fixed
  rank-one field* `K`, which is not the topology induced from `No[i]`. The
  article separates three questions that are routinely conflated — does an
  expression define a Hahn sum, do its partial sums converge in the intrinsic
  topology of a named field, and do they converge when every surreal scale is
  allowed as a test of smallness — and shows a yes to either of the first two
  does not give a yes to the third. §3.2 shows why higher rank cannot be
  silently scalarized.
- [`contours-and-stokes`](../contours-and-stokes/) already compares its
  integration categories with Berkovich, tropical, perfectoid, definable,
  tame and resurgent theories, and already observes that the Hahn field is a
  legitimate Berkovich base and that the Berkovich line is a tree with no
  planar Jordan circle. This article develops that comparison into a worked
  theory. It does not supply a map between coefficientwise contour pairings
  and Berkovich integration — `contours-and-stokes` is explicit that such a
  theorem would need extra hypotheses, and this article does not provide one.
- [`polynomial-algebra`](../polynomial-algebra/) supplies the finite-degree
  Newton profiles, valuation balls and residue-direction counts that the
  preparation and root-count sections extend to convergent infinite series.
- [`foundations`](../../foundations-and-computation/foundations/) is where
  `Σ t^(n^2) z^n` already appears, as the example showing that the all-scale
  rigidity theorem of `analysis` does not transfer to a fixed value group.
  This article credits it there and extends it, and its §12.5 confirms the
  reading recorded in the collection catalogue: at `Z = t^(−ω)` the exponents
  `n^2 − nω` strictly decrease, so the support is not well ordered and the
  series is *not* an all-surcomplex entire function. The obstruction **agrees
  with** proper-class all-scale rigidity rather than refuting it. The
  localization theorem from the same report is what licenses working in a
  fixed workspace at all.

## The gap claim, checked

The report claims a *documented, non-empty* gap — that the repository already
has a Berkovich comparison, and that what is missing is a developed rank-one
analytic theory — and it credits the `t^(n^2)` series to the repository.
Both halves were checked against the tree at commit `e260237`, and **both are
accurate**:

- Berkovich geometry is genuinely already present. `contours-and-stokes` has
  a dedicated subsection, *Berkovich geometry changes the space, not just the
  topology*, plus a second on Chambert-Loir–Ducros tropical Stokes theory, a
  row in its category-comparison table, and Baker–Rumely and Temkin in its
  bibliography; the topic also surfaces in `polynomial-algebra`. The report's
  refusal to claim the topic is absent is correct, and its README says so up
  front.
- What is genuinely absent is the development. Outside this directory, the
  strings *Tate algebra* and *affinoid* occur **nowhere** in `docs/`. No
  existing report constructs a Tate algebra, locates it among the coefficient
  rings, or works Berkovich disks, annuli and a nonpolynomial entire function
  through that category.
- The series credit is correct. `Σ t^(n^2) z^n` really does occur in
  `foundations-and-computation/foundations/article.tex` (line 2270, and in its
  source manuscript `06-classes-universes-and-lean-audit.tex`) and again in
  `foundations-and-computation/computer-algebra/article.tex`. It is the
  repository's example, cited as such.

## What it does not claim

Every limitation the report shipped with is kept here.

- An expository synthesis and mathematical continuation. **No priority
  claim**, and no claimed solution of a named published open problem. Imported
  inputs are identified — the Hahn construction and algebraic closedness
  (Poonen), the Berkovich point classification and the annulus deformation
  retraction (Temkin; Poineau–Turchetti). The support and convergence
  comparisons, the preparation argument, the root-count formulas, the residue
  computations and the case study are proved in the article.
- No topology or analytic spectrum is constructed on the proper class
  `No[i]`. No claim that an arbitrary set of surcomplex data sits inside a
  rank-one workspace preserving its natural valuation.
- No coefficientwise ordinary complex integral is identified with a path
  integral in a Berkovich spectrum.
- No arbitrary-radius complex exponential, global differential field, or
  universal decision algorithm.
- "Entire" means exactly the class defined in the article — every real
  valuation radius over the fixed `K`. It is **not** a synonym for every
  fine-local analytic class or every coherent Hahn atlas elsewhere in the
  collection. The derivative fixes `K`. All polynomial degrees are ordinary
  finite integers, all supports are sets, all norm radii are positive
  ordinary reals. These are hypotheses, not implementation limits.
- The finite checks are artifact and computation checks. They are **not** a
  proof-assistant verification of the general arguments, and none of the
  proofs has been formally verified. This is an AI-assisted draft, not
  refereed.
- The repository audit behind the article (`repository-audit.md`) was
  targeted: the catalogue, the relevant READMEs, and introductory and
  comparison material — not a line-by-line certification of every
  manuscript. An incomplete code-search response was not used as evidence of
  absence. A bibliography link is not a claim that the linked file was
  proof-audited.

## Build

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
latexmk -c
```

A standard TeX Live or MiKTeX installation with the packages named in the
preamble is sufficient. The bibliography and both TikZ diagrams are embedded;
there is no BibTeX step, no external figure asset, no shell escape, and no
repository checkout is needed. Last build: **30 pages**, 0 errors, 0
undefined references or citations, 0 LaTeX or package warnings, 0 overfull
and 0 underfull boxes. `build-report.md` records the rendering and
text-bounding-box inspection behind that build.

## Rerunning the finite checks

**Run these on a copy of the directory.** `code/verify-examples.py` writes a
JSON report, and pointing it at `data/` will overwrite a file that ships
verbatim as the recorded evidence. Copy the directory elsewhere first, or
send the output somewhere harmless:

```sh
python code/verify-examples.py --output "$TMPDIR/verification.json"
```

Python 3.10 or newer. Standard library only — `fractions.Fraction`
throughout, no floating-point arithmetic, no third-party packages, no
network.

What is recorded, and what has been rerun:

- `data/verification.json` is the delivered run: **542 checks, 542 passed**,
  under Python 3.13.5. It also carries the computed root expansions and every
  individual assertion. The article's own tally (§13.3) agrees: 542/542.
- The suite was **rerun for this collection and passed 542/542 again**, under
  Python 3.14.4. The shipped JSON still records 3.13.5, because it is the
  delivered artifact and was deliberately not overwritten.

Two quirks of the shipped evidence, neither of them a defect in the
mathematics:

- The script's `--output` default is `verification.json` **in the current
  working directory**, not `data/`. Run from the directory root it drops a
  stray file beside `README.md`; run from `code/` it drops one in `code/`.
  Give `--output` an explicit path.
- `data/verification-summary.txt` is captured stdout, not a file the script
  writes, and its last line still records the delivery-time path
  `/mnt/data/surreal_gap_work/deliverable/verification.json`. It is kept as
  delivered.

The README as shipped referred to these files by their delivery names
(`verify_examples.py`, `REPOSITORY_AUDIT.md`, `BUILD_REPORT.md`, and the
data files at the directory root). They were renamed and moved into `code/`
and `data/` on ingest to match the rest of the collection; the paths above
are the ones that exist.
