# Hahn-Valued Measures and Probability

**Strong atomicity, coefficientwise extension, and hidden negative mass**
Merged research report, 22 September 2026, from four manuscripts. Sources 10,
11 and 15 were written independently on that day, all pinned to repository
snapshot `4cf691c7d951e037739d32d9f5c387dcce724f3c`. Source 16 (manuscript 06
of a later delivery, the same day) is pinned to
`d22a5b35d5b3040e870c3cfd6d1c8f7259e094b0` and read the three-source version
of this report before writing.

```
article.tex   the report, standalone LaTeX with an internal bibliography
article.pdf   the compiled report, 86 pages
README.md     this guide
10-strong-hahn-measures-provenance.md                    source 10: repository and literature audit at its pin
15-infinite-products-of-probabilities-RESEARCH_AUDIT.md  source 15: repository and literature audit at its pin
code/         10-strong-hahn-measures-verify.py, 11-hahn-moments-verify.py,
              15-infinite-products-of-probabilities-verify.py,
              16-coefficientwise-measure-theory-verify_examples.py, and the
              four delivered build scripts *-build.sh
data/         10-strong-hahn-measures-verification.{json,txt},
              11-hahn-moments-verification_results.json,
              11-hahn-moments-verification_summary.txt,
              15-infinite-products-of-probabilities-verification.json,
              15-infinite-products-of-probabilities-build_summary.json,
              16-coefficientwise-measure-theory-verification_results.json,
              16-coefficientwise-measure-theory-build_validation.json
```

Every label in `article.tex` carries the prefix `meas:`. Source 16's material
carries the sub-prefix `meas:cw:`. **No pre-existing label was renamed or
removed**: the source had 250 `\label`s before this merge and has 324 after
it, all 250 still present. Sections 1–24 and every theorem number in them are
unchanged; the scope part moved from Sections 25–29 to Sections 32–36. The
programs, data files and audit records keep the source numbers as prefixes.
Source 11's and source 16's audits were sections of their articles; they are
summarized in Section 35. The source manuscripts themselves are not shipped.

## Two axioms, two spines

A **coefficientwise Hahn measure** is a Hahn series `Σ μ_γ t^γ` of ordinary
finite signed or complex measures with one well-ordered exponent set; disjoint
unions are added exponent by exponent, by ordinary absolutely convergent sums.
A **strong Hahn measure** requires the masses of every disjoint sequence of
events to be strongly Hahn summable. The report never writes a bare "Hahn
measure" or "Hahn probability" for a statement that holds in only one class.

- **Strong spine.** Sources 10 and 11 proved the same classification
  independently, from the same scalar lemma, and found the same counterexample
  weights and the same `ω+1` threshold. Each is printed once, crediting both.
  **Source 10 is the base**, for the weakest hypotheses (any countably
  separated space; no common support, divisibility, bounded variation or
  compactness). The common support is proved by source 11's deterministic
  row-selection lemma; source 10's randomized selection lemma is kept as a
  second route. Source 15 proved the classification again, with a common
  support *assumed* on compact metric spaces; that version is recorded as a
  special case, not as a more general theorem, and source 15's finite-orbit
  and exchangeability theorems are re-derived on countably separated spaces.
- **Coefficientwise spine.** Source 15: the two-axiom framing, the
  coefficientwise extension test, the null-ideal positivity criterion, and the
  `ℓ¹/ℓ²` product thresholds (Sections 19–24). Source 16: the class with
  **countably many exponents**, where one real control measure turns the
  null-ideal criterion into a pointwise inequality and supports integration,
  Radon–Nikodym, products and conditioning (Sections 25–31), plus a third
  reading of countable addition, by limits in the surreal order (Section 2.7).

## What the report claims

Let `Γ` be a set-sized ordered abelian group, **not assumed divisible** (only
the finite Gaussian quadrature theorem needs a real closed field).

**Strong class** (Parts II–IV).
- **Theorem 4.2** (sources 10, 11): on a countably separated space a real or
  complex strong Hahn measure is `μ(A) = Σ^H_{x∈A} w_x` for one strongly
  summable family; it extends uniquely to all subsets; it is positive iff every
  `w_x ≥ 0`. **Corollary 4.3**: a map is a strong Hahn measure iff each
  coefficient function is a finite combination of point masses, with no common
  support assumed. **Corollary 4.5**: on countably separated spaces the strong
  Hahn measures are exactly the coefficientwise ones with finitely atomic
  coefficients. **Corollary 4.6**: a strong Hahn probability has a finitely
  supported standard part. **Example 4.9**: countable separation cannot be
  dropped.
- **Theorem 6.1** (source 15, re-derived): invariant strong probabilities live
  on finite orbits; **Corollaries 6.2, 6.3**: no transitive invariant strong
  probability, and exchangeable strong laws are mixtures of constant sequences.
- **Theorem 8.2** (source 10): coherent cylinder data over finite alphabets
  extend strongly iff the combined support is well ordered and each exponent's
  active width is bounded in depth. **Theorem 10.1**: independent finite-state
  coordinates have a positive strong extension iff finitely many coordinates
  are random at the residue level and the individual rare entries are strongly
  summable; **Corollary 10.3** is the one-line Bernoulli case; **Theorem 11.1**:
  aggregating rare entries is insufficient; **Proposition 11.3**: enlarging the
  exponent group repairs nothing.
- **Theorem 12.2** (source 11): exact strong moment criterion on an ordinary
  real sample set (common well-ordered support, finite signed atomic rows,
  nonnegative reassembled weights). **Theorems 13.1, 13.4, 13.7**: finite
  visibility, polynomial barrier, continuous barrier.
- **Definition 14.1** prints once the weight pattern both sources found.
  **Proposition 14.2** (source 10): on Cantor space all cylinder masses are
  nonnegative, yet the unique strong extension has a negative singleton.
  **Theorem 14.3** (source 11): on `[0,1]` the functional is strictly positive
  on every nonzero Hahn polynomial nonnegative on `[0,1]`, extends to a
  positive functional on `C([0,1],R)`, and its unique strong representing
  measure has mass `−t` at `0`. **Theorem 15.2** (sources 10 and 11): in the
  strong class the least support order type admitting nonnegative finite tests
  with a negative event is `ω+1`, for cylinder tests (a) and polynomial tests
  (b).
- **Theorem 16.2** and **Corollary 16.3**: every Hankel determinant valuation
  and leading coefficient of the example, and Jacobi scales without a common
  support. **Theorems 17.1, 17.3**: positive Gaussian quadrature at every
  finite order, with a non-Archimedean node for every `N`.
  **Corollary 18.1**: the surreal form of the example.

**Coefficientwise class** (Part V).
- **Theorem 19.1** (source 15): signed extension of cylinder data is decided
  per exponent by total variation (Riesz–Markov). **Theorem 19.2**
  (`meas:thm:nullideal`, the canonical statement; source 15, and
  independently source 18): on an arbitrary measurable space, with any
  well-ordered exponent set, a real coefficientwise Hahn measure is positive
  iff each coefficient's negative part vanishes on the common null ideal of all
  earlier coefficients; for a countable predecessor set this is absolute
  continuity with respect to one control measure. **Example 19.5**: two
  exponents already give positive cylinders and a negative singleton.
- **Theorem 20.1**: weighted `ℓ²` rows at interior baselines; **Theorem 21.1**:
  `ℓ¹` rows at deterministic baselines; **Theorem 22.1**: the mixed case; all
  extensions positive on every Borel set. **Corollary 23.1**: an i.i.d.
  Bernoulli law extends iff its bias is real. **Example 23.3**: the uniform
  separation hypothesis of Theorem 20.1 is needed.
- **Countably many exponents** (source 16). **Theorem 25.3**: every such
  measure has a Hahn-valued density `θ` with respect to one finite real
  control, and is positive iff `θ ≥ 0` almost everywhere; a positive one has
  the null sets of the control. **Proposition 25.4** (added in the merge)
  states exactly how this relates to Theorem 19.2: for a countable exponent
  set, `θ ≥ 0` a.e. is equivalent to conditions (a)–(c) there, the null ideal
  `J_{<γ}` being the sets essentially inside `{θ_δ = 0 for all δ < γ}`.
  Source 16's sign lemma (**Lemma 25.2**) is kept as a second proof of
  Theorem 19.2 for countable exponent sets (**Remark 25.5**); Theorem 19.2
  alone covers uncountable ones, where no single control exists (**Example
  31.3**). **Remark 25.6**: `meas:cor:dominated` (Corollary 19.4) with a
  countable exponent set is the case where the leading law is itself a control
  and `θ` has leading coefficient 1; the density criterion also admits later
  coefficients not dominated by the leading law.
- **Theorems 26.2, 26.3**: Hahn–Jordan decomposition, with the order variation
  attained by a two-set partition; **Corollary 26.4**: a vector lattice over
  the countably supported field; **Proposition 26.5**: extension from a
  generating algebra, positivity only through the density.
- **Definition 27.3**, **Theorems 27.4, 27.5**: a density-adapted integral of
  Hahn-valued functions, independent of the control; **Theorem 28.1**: an exact
  Radon–Nikodym correspondence, even when the derivative has no common
  well-ordered support (**Example 27.2**); **Theorem 28.2**: Lebesgue
  decomposition; **Theorem 28.3**: coefficientwise dominated convergence;
  **Examples 28.4–28.6**: order-bounded functions need not be integrable,
  bounded convergence fails, and the positive cone is not coefficientwise
  closed.
- **Theorems 29.1, 29.2**: positive products and an adapted Fubini theorem.
  **Proposition 30.1**: conditioning activates the first scale that sees the
  event. **Theorem 30.4**: conditional expectation on the restricted
  σ-algebra; **Example 30.5**: it can leave the original integrable class;
  **Theorem 30.6**: in a bounded unit-leading class the usual projection laws
  hold. **Proposition 31.1**: equal infinitesimal point masses need finite
  additivity (numerosities).
- **Corollary 2.13** (source 16, from the foundations report's
  `found:thm:discrete`): additivity by limits in the surreal order allows only
  finitely many nonzero masses in each disjoint sequence.

## The two traps (Section 2.6)

1. **Threshold.** `ω+1` is the least support order type for hidden negative
   mass **in the strong class** (Theorem 15.2). In the coefficientwise class two
   exponents suffice (Example 19.5, same Cantor space, same cylinder tests).
   No contradiction: the coefficientwise example has an atomless leading
   coefficient, impossible for a strong measure.
2. **Finite shadow.** Only a **strong** Hahn probability has a finitely
   supported standard part (Corollary 4.6). Coefficientwise ones can have an
   atomless standard part (Theorem 20.1) or infinitely many atoms (Example 24.3).

## What the report does not claim

Section 32.2 lists every non-claim of every source (18 from source 10, 17 from
source 11, 15 from source 15, 25 from source 16) with the place where the
report keeps it. In particular:

- It is **not a first non-Archimedean Kolmogorov extension theorem**: Ludkovsky
  and Khrennikov proved one under different axioms. Source 10 said so; the
  statement is extended here to source 15's coefficientwise theorems, which
  did not cite them. It is not a first non-Archimedean probability theory and
  refutes no existing one (Benci–Horsten–Wenmackers, Brickhill–Horsten,
  Bottazzi, Kaiser, numerosities, the Levi-Civita measure).
- All negative strong-class results concern the strong axiom only; they do not
  exclude finitely additive, generalized-limit, coefficientwise, ultrametric,
  hyperfinite or ultrafilter probability. The interval example is not a
  counterexample to the classical real moment theorem.
- Source 16's theory needs **countably many exponents and finite real
  coefficient variation**. It is not a measure on the class of all surreals,
  not a length measure on surreal intervals, not a σ-finite theory (Lebesgue
  measure on `R` is not in it), and not a transfer of the real convergence
  theorems to the surreal order. Its conditional expectation need not stay in
  the original integrable class, and its "norm" is ordered-field-valued, not a
  Banach norm. Many of its steps reformulate classical scalar measure theory.
- The finite spectral theorem, Cauchy–Binet, Vandermonde interpolation,
  Gaussian quadrature, Riesz–Markov, Kakutani's `ℓ²` phenomenon, Neumann's
  lemma, normal forms, the scalar Radon–Nikodym, Fubini and conditional
  expectation theorems, and the embedding of set-sized ordered fields into
  `No` are classical inputs, not claims.
- The contributions are candidates: priority is not certified, no named
  published conjecture is claimed solved, and the report is not independently
  refereed or fully formalized. The
  [Lean coverage ledger](../../FORMALIZATION.md) records the checked strong
  atomicity core and product prerequisites, and, in the coefficientwise class,
  the null-ideal criterion (Theorem 19.2, with its control-measure form) and
  Corollary 19.4, each with its exact scope. The extension, moment and product
  results and all of Sections 2.7 and 25–31 still have pending work. The
  finite checks do not prove any infinite statement.

## Relation to neighbouring reports

- **[foundations](../../foundations-and-computation/foundations/)**: strong
  summability (`found:eq:summability`), the `n/(n+1)` example
  (`found:ex:boundedrankone`), the Neumann lemma (`found:sub:positivesupport`),
  `t^γ = ω^(−γ)` and workspace localization are cited, not reproved; so are the
  eventual constancy of convergent set-indexed nets (`found:thm:discrete`) and
  the absence of suprema (`found:sub:notdedekind`), which source 16 re-derived.
- **[physics](../../physics/surreal-scalars-and-spacetime/)**: its
  `phys:sub:probability` observed that equal infinitesimal weights are not
  strongly summable and asked for a summation theory; this report works out two.
  (Source 15 had reported that the repository had no `probability` matches;
  that was wrong as a statement about content, and is corrected in Section 1.5.)
- **[spectral theory](../../surcomplex/spectral-theory/)**: source 11's finite
  spectral lemma is replaced by citations of `thm:spectral` and
  `spec:thm:hermitian`.
- **[dynamics and normal forms](../../surcomplex/dynamics-and-normal-forms/)**:
  its non-claim N75 refuses a countably additive invariant probability on
  arbitrary subsets; Theorem 6.1 proves that in the strong class none exists for
  an ordinary action with only infinite orbits (Remark 6.5).
- **[Herglotz positivity](../../surcomplex/hahn-herglotz-positivity/)**: the
  coefficientwise class on the circle with Fourier moments and Toeplitz tests.
  Its source proved the null-ideal criterion independently; Theorem 19.2
  (`meas:thm:nullideal`) is the canonical statement, covering its hypotheses.
- **[finite surreal probability](../finite-surreal-probability/)**: finite
  probability over surreal fields, placed with source 16 and built on this
  report's strong/coefficientwise distinction; its uncountable-support example
  with a negative coefficientwise integral marks the countability boundary of
  Lemma 25.2 (Section 31.3).
- **[Prony reconstruction](../../surcomplex/prony-reconstruction-at-surreal-scales/)**
  and **[Markov generators](../markov-generators-at-every-scale/)** use
  "moment" and Markov structure in other senses; neither is used here.

## Maintained review

The review follows the scalar atomicity and common-support arguments through
the cylinder, product, moment, quadrature and coefficientwise proof chains.
It corrects the distinction between subfamilies and regroupings, and between
nonnegative cylinders and strictly positive polynomial tests. An elementary
coefficientwise positivity lemma now states the common-support and absolute
summability hypotheses used by the boundary and mixed product constructions.

The leading scalar measure does inherit positivity from cylinders by finite
total-variation approximation. It is positivity of the full Hahn-valued
measure that can fail. The revised text explains this distinction before the
null-ideal criterion, expands the finite-factor argument for infinite products,
and makes example exponent groups and the zero case of Cauchy–Schwarz explicit.
Historical provenance files remain unchanged; the current formalization
subsection supersedes the source deliveries' claims that nothing is Lean-checked.

**Merge of source 16.** Its notation was renamed where it collided with this
report's (density `θ` for its `m`, "common-support" for its "coherent",
`L¹_ad(μ)` for its `D(μ)`, `|σ|_ord` for its order variation, `t` for its
`ε`; Convention 25.1). Results it re-derived are printed once and credited to
both: the order-limit and supremum facts (foundations report), the support
calculus, the normal-form embedding, the two-scale obstruction (Example 19.5),
the classical shadow (Remark 2.10), conditioning on an event
(Proposition 24.2) and the uncountable atoms (Remark 4.8). Stale statements
corrected (Section 35.2): the page count it quoted, its description of the
Lean coverage as strong-only (the null-ideal criterion was already proved in
Lean at its pin), and missing citations of the foundations and physics
reports. It adds Questions 33.11 and 33.12 and answers none of the earlier
ones.

## Build and reproduce

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The PDF has 86 pages. The build has no errors, no LaTeX or package warnings,
no undefined or multiply defined references, and no overfull or underfull
boxes.

The four check programs use only the Python standard library (3.10 or later)
and exact rational arithmetic. **Run them on a copy of this directory**:
`10-strong-hahn-measures-verify.py` writes `verification.json` and
`verification.txt` into `data/` (unprefixed names, beside the delivered
records), and `11-hahn-moments-verify.py` writes into its own directory unless
`--output-dir` is given. `15-infinite-products-of-probabilities-verify.py` and
`16-coefficientwise-measure-theory-verify_examples.py` print to standard output
and write only with `--output`.

```sh
python code/10-strong-hahn-measures-verify.py
python code/11-hahn-moments-verify.py --output-dir rerun-11
python code/15-infinite-products-of-probabilities-verify.py --output rerun-15.json
python code/16-coefficientwise-measure-theory-verify_examples.py --output rerun-16.json
```

The recorded runs passed 5,135 (source 10), 682 (source 11), 1,009 (source 15)
and 1,722 (source 16) assertions. When source 16 was merged, all four were
rerun under Python 3.14.4 and reproduced these counts; source 16's output
matched its record apart from the Python version. One of source 15's checks is
tautological (it asserts that a hard-coded value is negative), and so are
source 16's 40 `RN support obstruction` checks (they multiply two hard-coded
monomials). The delivered `*-build.sh` scripts are kept byte-identical; they
refer to the source packages' own layouts and do not build this report.
`15-infinite-products-of-probabilities-build_summary.json` and
`16-coefficientwise-measure-theory-build_validation.json` are the sources'
own records of their 23-page and 29-page builds.

During the earlier maintained review, the three then-present programs passed
again under Python 3.13.14 on temporary copies (5,135, 682 and 1,009
assertions). The copied source hashes match the preserved programs. Outputs
remained outside the repository; the tautological check remains included in
source 15's historical total.

A subsequent integration check repaired five escaped-command control
characters in the finite-probability cross-link (`\texttt`, `\tfrac`,
`\ref`). Its fraction and corollary reference now render correctly. The
PDF rebuilt in three passes at 86 pages, with no warnings or box issues
in either the incoming baseline or repaired build; the changed paragraph
was inspected. This typesetting repair does not extend the mathematical
review to source 16's new claims. Delivered verification and audit files
were not modified.
