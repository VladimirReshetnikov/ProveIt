# Hahn-Valued Measures and Probability

**Strong atomicity, coefficientwise extension, and hidden negative mass**
Merged research report, 22 September 2026, from three manuscripts written
independently on the same day (batch sources 10, 11 and 15), all pinned to
repository snapshot `4cf691c7d951e037739d32d9f5c387dcce724f3c`.

```
article.tex   the report, standalone LaTeX with an internal bibliography
article.pdf   the compiled report, 64 pages
README.md     this guide
10-strong-hahn-measures-provenance.md                    source 10: repository and literature audit at the pin
15-infinite-products-of-probabilities-RESEARCH_AUDIT.md  source 15: repository and literature audit at the pin
code/         10-strong-hahn-measures-verify.py, 11-hahn-moments-verify.py,
              15-infinite-products-of-probabilities-verify.py, and the three
              delivered build scripts *-build.sh
data/         10-strong-hahn-measures-verification.{json,txt},
              11-hahn-moments-verification_results.json,
              11-hahn-moments-verification_summary.txt,
              15-infinite-products-of-probabilities-verification.json,
              15-infinite-products-of-probabilities-build_summary.json
```

Every label in `article.tex` carries the prefix `meas:`. The programs, data
files and audit records keep the batch numbers of the sources they came from.
Source 11's audit was an appendix of its article; it is summarized in
Section 28 of the report. The source manuscripts themselves are not shipped.

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
  `ℓ¹/ℓ²` product thresholds.

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

**Coefficientwise class** (Part V, source 15).
- **Theorem 19.1**: signed extension of cylinder data is decided per exponent
  by total variation (Riesz–Markov). **Theorem 19.2** (`meas:thm:nullideal`,
  the canonical statement; source 15, and independently source 18): on an
  arbitrary measurable space, with any well-ordered exponent set, a real
  coefficientwise Hahn measure is positive iff each coefficient's negative part
  vanishes on the common null ideal of all earlier coefficients; for a
  countable predecessor set this is absolute continuity with respect to one
  control measure. **Example 19.5**: two exponents already give positive
  cylinders and a negative singleton.
- **Theorem 20.1**: weighted `ℓ²` rows at interior baselines; **Theorem 21.1**:
  `ℓ¹` rows at deterministic baselines; **Theorem 22.1**: the mixed case; all
  extensions positive on every Borel set. **Corollary 23.1**: an i.i.d.
  Bernoulli law extends iff its bias is real. **Example 23.3**: the uniform
  separation hypothesis of Theorem 20.1 is needed.

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

Section 25.2 lists every non-claim of every source (18 from source 10, 17 from
source 11, 15 from source 15) with the place where the report keeps it. In
particular:

- It is **not a first non-Archimedean Kolmogorov extension theorem**: Ludkovsky
  and Khrennikov proved one under different axioms. Source 10 said so; the
  statement is extended here to source 15's coefficientwise theorems, which
  did not cite them. It is not a first non-Archimedean probability theory and
  refutes no existing one (Benci–Horsten–Wenmackers, Brickhill–Horsten,
  Bottazzi, Kaiser).
- All negative strong-class results concern the strong axiom only; they do not
  exclude finitely additive, generalized-limit, coefficientwise, ultrametric,
  hyperfinite or ultrafilter probability. The interval example is not a
  counterexample to the classical real moment theorem.
- The finite spectral theorem, Cauchy–Binet, Vandermonde interpolation,
  Gaussian quadrature, Riesz–Markov, Kakutani's `ℓ²` phenomenon, Neumann's
  lemma and normal forms are classical inputs, not claims.
- The contributions are candidates: priority is not certified, no named
  published conjecture is claimed solved, nothing is refereed, nothing is
  checked in Lean. The finite checks do not prove any infinite statement.

## Relation to neighbouring reports

- **[foundations](../../foundations-and-computation/foundations/)**: strong
  summability (`found:eq:summability`), the `n/(n+1)` example
  (`found:ex:boundedrankone`), the Neumann lemma (`found:sub:positivesupport`),
  `t^γ = ω^(−γ)` and workspace localization are cited, not reproved.
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
- **[Prony reconstruction](../../surcomplex/prony-reconstruction-at-surreal-scales/)**
  and **[Markov generators](../markov-generators-at-every-scale/)** use
  "moment" and Markov structure in other senses; neither is used here.

## Build and reproduce

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The recorded build has 64 pages, zero errors, zero warnings, zero undefined
references and zero overfull boxes.

The three check programs use only the Python standard library (3.10 or later)
and exact rational arithmetic. **Run them on a copy of this directory**:
`10-strong-hahn-measures-verify.py` writes `verification.json` and
`verification.txt` into `data/` (unprefixed names, beside the delivered
records), and `11-hahn-moments-verify.py` writes into its own directory unless
`--output-dir` is given. `15-infinite-products-of-probabilities-verify.py`
prints to standard output and writes only with `--output`.

```sh
python code/10-strong-hahn-measures-verify.py
python code/11-hahn-moments-verify.py --output-dir rerun-11
python code/15-infinite-products-of-probabilities-verify.py --output rerun-15.json
```

The recorded runs passed 5,135 (source 10), 682 (source 11) and 1,009
(source 15) assertions; a rerun during the merge (Python 3.14.4) reproduced
all three counts, with identical output apart from the recorded Python version
and line endings. One of source 15's checks is tautological (it asserts that a
hard-coded value is negative). The delivered `*-build.sh` scripts are kept
byte-identical; they refer to the source packages' own layouts and do not build
this report. `15-infinite-products-of-probabilities-build_summary.json` is
source 15's hand-written note on its own 23-page build.
