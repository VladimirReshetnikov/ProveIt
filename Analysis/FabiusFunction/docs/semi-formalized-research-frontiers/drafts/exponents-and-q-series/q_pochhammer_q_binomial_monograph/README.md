# q-Series and inverse q-analogs

This directory contains the one canonical document for forward q-series and
branch-aware inverse q-analog theory:
`q_pochhammer_q_binomial_monograph.tex`. Files under `chapters/` are implementation
units included by that master; they are not independent manuscripts.
The reader-facing structure has 28 numbered forward chapters, eight numbered
inverse chapters, and five appendices. The source-only validator's count of 13
chapter files refers to implementation inputs, not to the printed chapter
count.

The consolidation uses the former q-Pochhammer/q-binomial monograph as its
forward backbone and incorporates the former inverse-q synthesis as a
specialist part. The three general q-series guides were donor manuscripts:
their repeated results map to one strongest canonical statement, while only
genuinely stronger or independent material was transplanted. The completed
`source_concordance.csv` assigns every one of the 547 source result
environments a reviewed disposition. All five source-publication trees are
therefore historical inputs preserved by the pinned revision and repository
history, not parallel live packages.

The editorial contract is mathematical rather than mechanical:

- a repeated result is stated once, with the strongest proved hypotheses and
  one complete human-readable proof;
- an erroneous or overbroad assertion is corrected, split, or removed;
- an unproved assertion survives only when it is interesting, precise, and
  plausible, and then only in an explicitly labelled `Conjecture`
  environment;
- numerical and symbolic checks are evidence or regression tests, not
  substitutes for an infinite proof;
- exact Lean counterparts, partial Lean infrastructure, complete human proofs,
  source records, and conjectures are reported as distinct statuses.

## Provenance and reproducibility

`theorem_concordance.csv` and `audit/SOURCE_REVISION` retain the already
reviewed 260-row history of the six precursor inverse-q packages at commit
`6fe9fb8f50e1b8a9a800fa0e8ef6f688f5bb5838`. Those historical source paths
are immutable. `source_concordance.csv` is the completed 547-row disposition
ledger for the five-publication merge surface pinned by
`audit/MERGE_SOURCE_REVISION` at commit
`9560165ae2eb33590404a090ab26bd3ca715f32f`. The ledgers remain separate so
the earlier six-package inverse provenance is not silently reinterpreted.

The migrated `assets/` tree preserves six experiment programs, nineteen
CSV/TXT outputs, and fourteen vector figures selected by the historical
77-row `assets/ASSET_DISPOSITION.csv`. Its active `assets/SHA256SUMS` has 43
entries because it also covers asset metadata and environment files; this is
not a contradiction with the 39 retained historical payloads.

## Validation state

The source-structure gate is:

```text
python audit/validate_canonical.py
```

It checks the complete input graph, balanced environments, unique labels,
resolved references, immediate one-to-one ownership of a nonempty proof by
every proved result, both concordances---the 260-row inverse ledger and the
completed 547-row five-publication ledger---and reproduction of both pinned
source inventories.  Canonical status describes the destination, not the
donor's editorial disposition: a proved row with a live result destination
may never be marked `not applicable`, even when the donor copy was retired.
The larger ledger is reproduced, including all editorial columns, with

```text
python audit/extract_merge_sources.py
```

and may be regenerated explicitly with `--write-reviewed-csv`.  That write is
atomic, is tied to `audit/MERGE_SOURCE_REVISION`, and fails if any editorial
override does not match its pinned source exactly once.

The fifteen status-labelled archival identity records have a separate exact
finite check:

```text
python audit/verify_archival_identity_records.py
```

It compares all coefficients through degree 100 using integer arithmetic:
1,515 equalities in total. This is a transcription-quality gate, explicitly
not an infinite proof of any recorded identity.

The exhaustive package checksum gate is:

```text
python audit/build_package_checksums.py --check
```

It checks every permanent package file except the self-referential root
`SHA256SUMS` ledger itself. The nested asset ledger remains independently
useful because it preserves the migrated experiment and research-figure
boundary.

The retained `q_pochhammer_q_binomial_monograph.pdf` is a 354-page A4
build checkpoint made from the then-current source (14,381 lines, 675,239 bytes,
SHA-256 `240bff72fb47562e9a8fd87085b5a3a96d738189714518db17988f7c4ac15d31`).
The PDF is 3,030,302 bytes with SHA-256
`1050a9a3b0b7a8df8e7de0870946ae64940d7d7839a2f20427be0ebe14b0ba8c`.
It was built by exactly three serial
`pdflatex -interaction=nonstopmode -halt-on-error` passes, which produced 343,
354, and 354 pages, with `makeindex` run on the `.idx` file after each pass.
The final log scan found three overfull boxes, all in the single paragraph of
the `QPochhammerEntire` crosswalk, whose long declaration names lack break
points. All pages are A4. `pdffonts` reports 42 font rows, all embedded and
subsetted, including five Libertinus rows, with no Type-3
fonts. The files under `assets/experiments/**/figures/` remain research
figures, not publication manuscripts.

The current master TeX is a source-only successor to that checkpoint: it has
14,390 lines, 675,892 bytes, and SHA-256
`cd8e5830fca13f85fb614d4ce7e0b6c1c99a6da54c660c76df2c6890def69ae3`.
It combines the incoming q-beta and Newton-interpolation crosswalks with the
Gaussian coefficient closure already on this branch. The regenerated root
`SHA256SUMS` ledger records the live source and retained PDF separately; the
PDF remains pinned to source SHA-256
`240bff72fb47562e9a8fd87085b5a3a96d738189714518db17988f7c4ac15d31`
and does not claim render parity with the merged TeX.

The current source includes exhaustive crosswalks for `QPochhammerEntire`
(zero definitions
and five legacy compatibility theorems), `QPochhammerInfinite` (one definition
and twenty-nine theorems), `QPochhammerDissection` (zero definitions and two
theorems), `QBinomialTheoremInfinite` (one definition and twenty-two
theorems), `GaussianBinomialPalindromic` (zero definitions and fourteen
theorems), `GaussianBinomialPolynomialStructure` (zero definitions and five
theorems), and `GeometricPochhammerNormalConvergence` (zero
definitions and three theorems). The wider inventory also includes
`QMultinomial` (one definition and nine theorems),
`QPochhammerInfiniteBounds` (zero definitions and five theorems),
`QPochhammerComplexOrder` (one definition and four theorems),
`BasicHypergeometricSeries` (two definitions and five theorems),
`HeineTransformation` (two definitions and five theorems), and
`QGaussSummation` (zero definitions and two theorems). Recent exact surfaces
add `QExponential` (three definitions and eight theorems), `JacksonIntegral`
(one definition and seven theorems), `ThetaQuasiPeriodicity` (one definition
and six theorems), `QPochhammerLogDerivative` (zero definitions and ten
theorems), `QPochhammerOrderDerivative` (zero definitions and three theorems),
`JacobiCubic` (zero definitions and two theorems),
`CentralQBinomialReduction` (zero definitions and six theorems), and
`CyclotomicFactorization` (zero definitions and seven theorems), together with
expanded Euler, Jacobi, and Rogers--Szegő material. The newest arithmetic
surfaces are `PrimitiveRootBlock` (zero definitions and three public theorems),
`QLucas` (zero definitions and eight public theorems), `QCatalan` (one definition and
eleven theorems), and `CyclotomicDivisibility` (zero definitions and three
theorems). The incoming formal surfaces also include `NewtonInterpolation`
and `QBetaIntegral`, covering arbitrary-node and geometric-grid Newton
interpolation, the Jackson q-beta product, its q-gamma quotient, positivity,
symmetry, and recurrences.
The collision-free polynomial API is `nodeNewtonPoly`,
`nodeNewtonPoly_succ`, `eval_nodeNewtonPoly`,
`degree_nodeNewtonPoly_lt`, `nodeNewtonPoly_eq_interpolate`,
`eq_nodeNewtonPoly_of_eval_eq`, and `coeff_nodeNewtonPoly_self`; the remaining
eight Newton declarations retain their incoming names.

The two newest generic theorems are
`deriv_qPochhammerInfIn_ne_zero_of_mul_pow_eq_one`, which gives a nonzero
derivative at every raw factor zero `a*q^j = 1` including `q = 0`, and
`analyticOrderAt_qPochhammerInfIn_of_eq_zero`, which gives analytic order
exactly one at every zero. The `QPochhammerEntire` wrappers retain the older
`complexQPochhammerInf` names by transferring the generic local-uniformity,
entireness, zero-locus, reciprocal-power, and analytic-order results rather
than duplicating their analytic proofs. In `QBinomialTheoremInfinite`,
`finiteQPochhammerIn_zero_left` remains the unique declaration owned by
`GaussianBinomialAtOne` and is imported rather than redeclared. The forward
status ledger is 81 Exact, 85 Partial, 108 None, and 8 interface rows; the
original 191-result pre-Fabius core is 36/29/123/3, and the
completed source concordance records 66 Lean-proved rows, 412 human-proved
frontier rows, 60 not-applicable rows, and 9 conjectures.
The fourteen-theorem `GaussianBinomialPalindromic` API and five-theorem
`GaussianBinomialPolynomialStructure` API give exact degree,
monicity, constant and top coefficients, reflection, coefficient
palindromicity, and the division-free mean identity over generic commutative
semirings. Its new `coeff_gaussianBinomial_one_of_pos_of_lt` and
`coeff_gaussianBinomial_one` theorems prove the strict-interior coefficient
of `q` is one and give the total formula with every boundary zero. Thus
`cor:positivity`, `thm:qbinom-structure`, and the inverse-source proposition
`prop:gq-positive-palindromic` are Exact. The compound
outer spectral-product theorem remains Partial even though the three-theorem
outer-product leaf proves local-uniform (normal) convergence for every complex
strict contraction, including `q = 0`, together with the nome-`1/4` Rvachev
and bounded-Fabius Fourier specializations. Its named centered/MGF packaging,
exterior reciprocal formula, pole divisor, and zero--pole exchange remain
outside Lean.
The new status changes record the exact q-exponential eigenfunction and
Jackson integration-by-parts subclaims, and Partial formalizations of the
q-exponential factorization, Jackson fundamental theorem, and theta
quasi-periodicity; the remaining clauses named in their rows stay explicit.
The incoming tail further makes the full elementary Gaussian-polynomial
structure and Jacobi's cubic identity Exact, while adding Partial order
derivative and Gaussian-moment rows; the Lambert logarithm row remains
Partial with both displayed derivative formulas now formalized.
The central-reduction row is now Exact through a division-free commutative-ring
identity and its field quotient wrapper; the cyclotomic-factorization row is
Exact over every commutative ring for the factorial form and every integral
domain for the Gaussian form, with the exponent bounds stated explicitly. The
half-base Gaussian valuation row remains Partial: Lean proves the reciprocal
identity and symmetry used in the argument, while the concluding odd-integer
valuation statement is still outside the formal surface.

The complete root block, evaluated q-Lucas theorem, square-free cyclotomic
criterion, and q-Catalan row are Exact. The primitive-root value in the
Babbage corollary is formalized over every integral domain, while its
derivative clause keeps that compound row Partial.

The geometric Newton interpolation and divided-difference rows are Exact. The
Jackson q-beta product/q-gamma evaluation and its two recurrence formulas are
also Exact. No PDF was generated locally while resolving this merge: the
supplied 354-page artifact is the validated upstream receipt described above,
while the merged source is its source-only successor.
