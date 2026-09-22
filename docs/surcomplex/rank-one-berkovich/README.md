# Rank-One Non-Archimedean Analytic Geometry inside the Surcomplex Numbers

**Tate algebras, Berkovich disks, analytic annuli, and an entire-function
case study**

One standalone research article, `article.tex` (31 pages compiled), with
`code/` and `data/` holding the exact finite checks and their recorded
output. Not a merge: it is a single delivered manuscript.

## What the report is

It works in a **fixed rank-one workspace**

    K = C((t^R)),   t^gamma = omega^(-gamma)  (Conway's monomial map),
    |a|_v = exp(-v(a))                        (a real-valued absolute value)

and asks what non-Archimedean analytic geometry over `K` actually looks
like. The real value group gives a real-valued non-Archimedean norm; spherical
completeness implies metric completeness, and the divisible value group and
algebraically closed coefficient field give algebraic closedness (Poonen's
Corollary 4). Thus `K` is a legitimate base for Tate algebras and Berkovich
spaces. Convergence here is **intrinsic norm convergence in this workspace**.
It is distinct from coefficientwise strong Hahn summation and from convergence
in the full fine topology of `No[i]` (see *Where it sits*, below).

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

- [`analysis`](../analysis/) establishes that every set of surcomplex numbers
  is closed and discrete in the **full fine topology**. Consequently an
  ordinary sequence converging there is eventually constant; this does not
  prohibit convergence in other specified topologies. Here convergence is in
  the *intrinsic valuation topology of the fixed
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

## The historical gap audit

The original report identified a developed rank-one analytic theory as a gap
in the inspected tree at commit `e260237`, while acknowledging its existing
Berkovich comparison and crediting the `t^(n^2)` series to the repository.
The accompanying audit records that snapshot and its targeted scope; it is
not an exhaustive absence claim about the current collection.

- Berkovich geometry is genuinely already present. `contours-and-stokes` has
  a dedicated subsection, *Berkovich geometry changes the space, not just the
  topology*, plus a second on Chambert-Loir–Ducros tropical Stokes theory, a
  row in its category-comparison table, and Baker–Rumely and Temkin in its
  bibliography; the topic also surfaces in `polynomial-algebra`. The report's
  refusal to claim the topic is absent is correct, and its README says so up
  front.
- The identified gap was the sustained development: construction of a Tate
  algebra, its place among the coefficient rings, and the joint treatment of
  Berkovich disks, annuli and a nonpolynomial entire function. This describes
  the comparison made in the pinned audit, not a current lexical search.
- The series credit is correct. `Σ t^(n^2) z^n` really does occur in
  `foundations-and-computation/foundations/article.tex` and again in
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

## Maintained proof review

The 22 September 2026 review followed the full main-text proof chain: spherical
completeness and convergence, the ring comparisons, Banach division and
preparation, zero counts, seminorm points, norm profiles, disk and annulus
primitives, the annulus retraction, canonical products, and the partial-theta
root and tail calculations. The main results remain intact.

The maintained text adds the nonzero hypothesis needed for a logarithmic norm
profile, states the domain of residue reduction in the root-count theorem,
explains uniqueness for the extended division operators, and derives the
constant-one seminorm bound from the usual boundedness definition. The product
proof now defines `G = Z^m ∏(1−Z/α_j)` explicitly and cancels its prepared
polynomial on each disk before invoking zero-free rigidity. The theta proof
justifies the quadratic error locally at `U = −1`, where its finitely many
negative powers are analytic.

Targeted primary checks confirmed the field import in
[Poonen, Corollary 4](https://math.mit.edu/~poonen/papers/amsval.pdf), the spectrum
definition in [Temkin v2, Definition 2.2.2.1](https://arxiv.org/pdf/1010.2235v2),
and the point classification and annulus retraction in
[Poineau–Turchetti v1, I.2 and I.7](https://arxiv.org/pdf/2010.09043v1).
The latter's open-annulus retraction restricts over a closed skeleton interval
to the closed-annulus setting here. The first normalized root equals the
negative of the series in [Sokal v1, Eq. (1.7)](https://arxiv.org/pdf/1106.1003v1).
These are checks of the stated imports, not full proof audits of those papers.

Historical `repository-audit.md`, `build-report.md`, `code/`, and `data/` remain
unchanged. The maintained article and this README correct the earlier broad
convergence wording and label the original repository audit as historical.

## Build

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
latexmk -c
```

A standard TeX Live or MiKTeX installation with the packages named in the
preamble is sufficient. The bibliography and both TikZ diagrams are embedded;
there is no BibTeX step, no external figure asset, no shell escape, and no
repository checkout is needed. The reviewed PDF was built with three passes of
`pdflatex -interaction=nonstopmode -halt-on-error` in a temporary output directory:
**31 pages**, 0 errors, 0
undefined references or citations, 0 LaTeX or package warnings, 0 overfull
and 0 underfull boxes. The 30-page baseline also had no warnings or boxes;
affected revised pages were rendered and inspected. The preserved
`build-report.md` records the original 30-page delivery build, not this review.

## Rerunning the finite checks

**Run these on a copy of the directory.** `code/verify-examples.py` writes a
JSON report, and pointing it at `data/` will overwrite a file that ships
verbatim as the recorded evidence. Copy the directory elsewhere first, or
send the output somewhere harmless:

```sh
python code/verify-examples.py --output /tmp/berkovich-verification.json
```

Python 3.10 or newer. Standard library only — `fractions.Fraction`
throughout, no floating-point arithmetic, no third-party packages, no
network.

What is recorded, and what has been rerun:

- `data/verification.json` is the delivered run: **542 checks, 542 passed**,
  under Python 3.13.5. It also carries the computed root expansions and every
  individual assertion. The article's own tally (§13.3) agrees: 542/542.
- The suite was **rerun during the maintained review and passed 542/542 again**, under
  Python 3.13.14. The shipped JSON still records 3.13.5, because it is the
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

The original delivery referred to these files by their delivery names
(`verify_examples.py`, `REPOSITORY_AUDIT.md`, `BUILD_REPORT.md`, and the
data files at the directory root). They were renamed and moved into `code/`
and `data/` on ingest. The maintained article now uses the current paths and
directs rerun output to `/tmp`; the preserved `build-report.md` retains its
delivery names.
