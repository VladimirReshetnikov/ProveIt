# Positivity without a Positive Measure

**Hahn–Herglotz normalization and strict moment hierarchies in surcomplex analysis**
Single-source research report, 22 September 2026, built from one manuscript
of batch 18 (`surcomplex_hahn_positivity`), pinned to repository commit
`4cf691c`. Prepared for Vladimir Reshetnikov.

This directory holds one manuscript. It is not a merge: there was no second
source, and nothing was selected out of a larger body of work. One proof is
printed elsewhere instead of here: the transfinite null-ideal criterion is
proved once in the collection, in the measures report (see below).

```
article.tex        the report, standalone LaTeX with an internal bibliography
article.pdf        the compiled report, 33 pages (title, contents, 31 numbered pages)
README.md          this guide
research_audit.md  the source's own repository and literature audit, as delivered
code/              verify.py (exact SymPy checks), build.sh (the source's build script)
data/              verification.txt (the source's recorded run), requirements.txt
```

Every label in `article.tex` carries the prefix `herg:`. Each of the source's
79 labels is kept, unchanged after the prefix, and six were added (`herg:sec:position`,
`herg:sec:conventions`, `herg:sec:nonclaims`, `herg:app:provenance`,
`herg:app:pinned`, `herg:app:notation`). `code/`, `data/` and
`research_audit.md` are byte-identical to the delivery.

## What the report claims

Let `Γ` be a nonzero set-sized ordered abelian group, `F_Γ = R((t^Γ))` and
`K_Γ = C((t^Γ))`. Coherent functions on an ordinary connected domain `U` form
`O(U)((t^Γ))`, and `U^#` is the halo of `U` (ordinary points plus arbitrary
infinitesimals), as in the analysis report. **`Γ` is assumed divisible only in
Theorems 3.3 and 3.5**; the source made divisibility a standing hypothesis,
but it is used only there, for the Hermitian congruence `L*PL = I_r ⊕ 0`
(Section 2.1, "Where divisibility is used").

A *moment* is always a Fourier moment `c_n = ∫ ζ^(−n) dμ` on the ordinary
circle, with values in `K_Γ`. Every measure is a **real-valued coefficientwise
Hahn measure** `μ = Σ ν_γ t^γ`: one well-ordered support, an ordinary finite
signed regular Borel measure at each exponent, countable additivity exponent
by exponent, and no strong Hahn summability (Definition 4.1).

- **Hahn–Herglotz normalization (Theorem 3.3, `Γ` divisible).** A matrix
  coherent function `H` with `Re H(a) ⪰ 0` at ordinary points is constant-congruent,
  after subtracting one constant Hermitian `iB`, to `G ⊕ 0` with `G(a₀) = I`,
  `Re G₀ ≻ 0` on `U`, and otherwise unrestricted higher coefficients.
  Positivity at ordinary points is equivalent to positivity on `U^#`, and
  `ker Re H(z) = ker P` on the whole halo. The scalar mechanism (Lemma 3.1,
  Corollary 3.2) needs no divisibility.
- **Harnack comparison (Theorem 3.5).** Any ordinary `C > C₀` works; the sharp
  classical constant need not, witnessed by `(1+z)/(1−z) + εz`.
- **Null-ideal criterion (Theorem 4.2).** A coefficientwise Hahn measure is
  positive iff each `ν_γ⁻` vanishes on the common null ideal of the earlier
  total variations; for a countable predecessor set this is `ν_γ⁻ ≪ λ_<γ` for
  an explicit control measure. This is **the same theorem as
  `meas:thm:nullideal`** of the measures report, found independently in the
  same batch; the main equivalence is proved there, and this report proves the
  translation between the two forms and the control-measure reformulation.
  Corollary 4.3: `ν₀ + εν₁ ≥ 0` iff `ν₀ ≥ 0` and `ν₁⁻ ≪ ν₀`. Example 4.4
  (this source's own): an uncountable, Dirac-led positive measure that every
  countable control measure would wrongly reject.
- **Strictly positive functionals without positive measures (Theorem 5.1,
  Corollary 5.2).** `Λ_ε(F) = (1+ε)∫F dm − εF(1)` is strictly positive, unital
  and pointwise completely positive on `C(T,C)((t^Γ))`, but has no positive
  coefficientwise representing measure.
- **Representation tests (Theorems 5.3, 5.4; Proposition 5.5).** Finite
  Toeplitz positivity is insensitive to arbitrary infinitesimal tails; a
  signed coefficientwise measure exists iff each exponent's functional is
  bounded on trigonometric polynomials, a coefficientwise distribution iff
  each exponent has polynomial Fourier growth; positive measures give
  `T_N ⪰ 0`.
- **The explicit obstruction (Theorems 6.1–6.4, Corollary 6.5).** For
  `c₀ = 1`, `c_n = −ε` (`n ≠ 0`): `T_N = (1+ε)I − εJ ≻ 0` with determinant
  `(1+ε)^N (1−Nε)` for every ordinary `N`, yet the unique signed
  representing measure is `(1+ε)m − εδ₁`, negative on `{1}`. Positive
  root-of-unity quadratures and fixed-Haar Fejér densities converge
  coefficientwise weak-* to it; the Schur parameters are
  `α_n = −ε/(1−nε)`, with internal poles of standard part 1, and
  `H_ε(1−ε) = −1 + 2ε`; a cyclic algebraic unitary has these moments and no
  positive coefficientwise spectral measure.
- **Strict hierarchy (Theorem 7.1).** `P ⊊ M ⊊ D ⊊ A ⊊ H` (positive measure,
  signed measure, distribution, Toeplitz-only, halo-Herglotz), every witness
  using only the exponents `0, η`. Example 7.2 lies outside this universe;
  Theorem 7.3 extends any finite infinitesimal prefix in all five ways.
- **Transport (Proposition 8.1)** to set-sized subfields of `No[i]`; with
  `ε = ω⁻¹` Theorem 6.1 becomes an explicit surreal statement.

## What the report does not claim

Section 8.4 lists 26 non-claims: 23 from the source, all kept where the
source made them, and 3 added when the report joined the collection. In brief:

- No named published conjecture is claimed settled. The package is a
  **candidate** original contribution; priority and absence from every
  repository file are not certified. Not refereed; no Lean.
- The boundary is the **ordinary** circle (or compact Hausdorff space) with
  coefficientwise additivity. Nothing is asserted about measures on an
  enlarged non-Archimedean circle, finitely additive or internal nonstandard
  representations, or other integration theories; Halpern, Bottazzi and
  Restrepo Borrero–Shamseddine are neither ruled out nor contradicted.
- Classical inputs are credited, not claimed: the Gesztesy–Tsekanovskii
  constant-kernel lemma, Riesz representation, Fourier uniqueness, the
  distribution growth criterion, real-closed congruence, Herglotz and Harnack.
- The **sharp classical Harnack constant need not survive**; only strict slack
  is proved.
- The moments `c₀ = 1`, `c_n = −ε` show that every finite Toeplitz test can
  pass while the unique signed representing measure is negative on `{1}`,
  and only because `ε` is infinitesimal: for a fixed positive real `ε`,
  `1 − Nε` eventually fails, so there is no counterpart over `R`. Enlarging
  the exponent group within the coefficientwise model cannot restore
  positivity.
- Normalization classifies halo positivity, not a boundary measure. The halo
  is not the internal disk. Weak-* limits are coefficientwise, not fine; the
  order bound of Theorem 5.1 is not fine continuity; `C(X,C)((t^Γ))` is not
  claimed to be a C*-algebra; no Hilbert completion or spectral theorem over
  `No[i]`; the Schur result does not forbid other function notions; bounded
  Fourier coefficients are not claimed sufficient for a measure.
- Example 7.2 is not an analytic counterexample on a positive-radius disk;
  Theorem 7.3 is not an undecidability claim.
- **No matrix-valued null-ideal criterion**, no full-disk classification.
- The finite checks prove nothing quantified over all sizes, all Borel sets,
  all holomorphic functions or arbitrary supports.
- Added in the collection: nothing is claimed about Theorems 3.3 and 3.5 for
  nondivisible `Γ`; Theorem 5.1(b), Remark 2.2 and Theorem 4.2 carry the
  credits below; **nothing here concerns strongly additive Hahn measures**.

## Relation to the neighbouring reports

**[analysis](../analysis/)** — prior results the source did not cite. Its
halo `c:p4:def-halo` is the halo used here, and Remark 2.2 (the halo misses the
boundary monad; `1 − ε`) is its `c:p4:rk-notball`. Its `c:p5:positivity`
(a pointwise-nonnegative Hahn family on an interval has positive coefficientwise
integral, via the least nonzero coefficient function) is the mechanism of
Theorem 5.1(b), which is therefore not new in mechanism; parts (c) and (d) are
what that theorem adds. Its `e:thm-poisson` recovers coherent harmonic
functions from boundary data given as a Hahn family of **continuous**
functions and "says nothing about" other boundary data. This report works past
that scope sentence and in the other direction, from halo positivity or
Toeplitz positivity to measure or distribution boundary data. That sentence
is a non-claim, not a posed problem, and nothing here answers a question
asked there.

**[hahn-valued-measures-and-probability](../../surreal/hahn-valued-measures-and-probability/)**
— the measure-theoretic companion, written in the same batch. Its central
class is **strong** Hahn measures, and it also treats the coefficientwise
class used here. The canonical null-ideal theorem is its `meas:thm:nullideal`.
Keep the classes attached to their thresholds: **in the strong class**,
cylinder or polynomial-square positivity forces positivity for support order
type at most `ω`, and `ω+1` is the least bad type; **in the coefficientwise
class**, a two-element support already fails (Theorem 6.1). Its strong,
interval, power-moment counterparts of Theorem 5.1 and Corollary 6.5 differ in
class, sample space and moment type.

**[spectral-theory](../spectral-theory/)** and
**[infinite-dimensional-hahn-spectral-theory](../infinite-dimensional-hahn-spectral-theory/)**
supply no spectral measures. Corollary 6.5 adds only negative information and
supplies none. **[trigonometry](../trigonometry/)** has the root-of-unity
orthogonality `trigonometry:eq:orthogonalityfinite` behind Theorem 6.2, and
**[foundations](../../foundations-and-computation/foundations/)** the Neumann
support lemma `found:sub:positivesupport`. The "moments" of
**[prony-reconstruction-at-surreal-scales](../prony-reconstruction-at-surreal-scales/)**
are finite power sums with Hahn-valued nodes, not Fourier moments.

## Stale statements corrected

The source's audit was made at its pin; `research_audit.md` keeps it as
delivered, and Appendix A.2 of the article corrects it. At the pin, the
reader map listed 26 reports and `docs/new` held 18 archives. Those archives
have since been unpacked into reports and `docs/new` emptied, and the two
"infinite-spectral" and "Hahn–Hilbert" archives are now the two parts of
`infinite-dimensional-hahn-spectral-theory`. The source's negative searches
for "Herglotz" and "Toeplitz" still hold: `git grep` finds neither word under
`docs/` at the pin, and at the placement commit `e9a9650` only in this
report's files. The source missed the analysis-report results above and,
because it was written in the same batch, the measures report.

## Build and reproduce

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
python -m pip install -r data/requirements.txt
python code/verify.py
```

The recorded build has no errors, no undefined or multiply-defined
references, no duplicate PDF destinations and no overfull boxes. A clean
compile proves nothing about the proofs.

`code/verify.py` needs Python 3.10 or later and SymPy (pinned 1.14.0). It uses
a formal `ε`, prints to standard output only, and **never rewrites**
`data/verification.txt`, which is the source's captured run under Python
3.13.5. It checks the Toeplitz determinant and eigenspaces (`N ≤ 8`), the
Cayley quotient and symbolic Schur recursion, both internal boundary values,
the `n²` example and negative `T₁`, distribution Fourier signs, root-of-unity
quadrature moments (`M ≤ 12`), the Fejér kernel, and the finite null-ideal
equivalence on all `3⁹ = 19,683` three-level, three-atom arrays (`2,744`
positive). Rerun for this report under Python 3.14.4 and SymPy 1.14.0, it
printed the same nine `PASS` lines and counts; only the Python version string
differs.

`code/build.sh` is the source's script. It changes to its own directory,
runs `pdflatex` three times, writes `build-pass-1.log`…`build-pass-3.log` and
overwrites `article.pdf`. As placed under `code/` it does not find
`article.tex`; to use it, copy this directory and put the script beside
`article.tex` in the copy.
