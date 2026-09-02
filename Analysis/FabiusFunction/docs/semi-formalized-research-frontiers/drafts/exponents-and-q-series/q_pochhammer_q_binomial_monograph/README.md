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
environments a reviewed disposition. This immutable merger ledger's reviewed
canonical-status totals remain 73 Lean-proved rows, 405 human-proved frontier
result rows, 60 not-applicable rows, and 9 conjecture rows. All five
source-publication trees are
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

After the pending parity rebuild, the final release-checksum gate is:

```text
python audit/build_package_checksums.py --check
```

It checks every permanent package file except the self-referential root
`SHA256SUMS` ledger itself. At this post-aed source checkpoint the root ledger
is deliberately marked `PARTIAL/PENDING`: it retains only hash-valid stable
payload rows and the verified historical PDF row, while omitting the mutable
README, provenance, and live master. It does not assert source/PDF parity, and
the command above is not a release gate until a final build regenerates the
exhaustive 70-row ledger. The nested asset ledger remains independently useful
because it preserves the migrated experiment and research-figure boundary.

The retained `q_pochhammer_q_binomial_monograph.pdf` is a verified historical
357-page A4 publication receipt from before the aed source integration. Its
14,635-line, 688,123-byte source had SHA-256
`30a75dde89df2c1b7b5f5e2b7188ec4dfc17c498aa4ae6c65cf1c6062310ad6b`;
the 2,270,834-byte PDF has SHA-256
`3673b2cb7d617ccbcc9e3c32af17dbb9f4e8d8c16882d889d2a299bd128e0593`.
After a clean sidecar state, exactly three serial
`SOURCE_DATE_EPOCH=1788242400 pdflatex -interaction=nonstopmode
-halt-on-error` passes produced 346, 357, and 357 pages. `imakeidx` invoked
`makeindex` in each pass; the stable index accepted 164 entries, rejected
none, and wrote 254 lines without warning.

The final log has no TeX errors, undefined references or citations, or rerun
request. Its only layout diagnostics are the three known overfull boxes in
the long `QPochhammerEntire` identifier paragraph at source lines 647--665.
Every page is A4 with zero rotation, and an 18-dpi raster audit found ink on
all 357 pages (the sparsest page still had 193 non-white pixels). The title,
author, subject, and keyword metadata match the source; both PDF dates resolve
to the fixed epoch, 2026-09-01 06:00:00 UTC. `pdffonts` reports 42 rows, all
embedded and subsetted, including five Libertinus rows, with no Type-3 font.
A representative contact sheet of pages 1, 5, 13, 140, 253, 273, 319, and 357
was inspected for complete rendering, including the cover, contents,
theorem-heavy pages, inverse material, the formalization appendix, and index.

Before that build, both the local remote-tracking ref and remote
`origin/main` were pinned to
`5e3fe8fcb99d0662096fe39c436d51a6ec7c1169`; the clean working HEAD
`191cce0e849a330f173c25be2b9f2f4cd7c2f211` had that checkpoint as a merge
parent. The mandatory post-build check observed that `origin/main` had moved
to `e6f3308dc377baa46aaa9463f0ae6fe9451d5ee2`. The subsequent integration
through `aed11fdf2738210f235490ba3477f134bba80aed` changes the live master,
so the source and PDF hashes above are preserved only as a matched historical
receipt. The live source has no current render-parity claim; a fresh final
build, audit, and exhaustive ledger regeneration are pending. Files under
`assets/experiments/**/figures/` remain research figures rather than
publication manuscripts.

An independent lexical audit of the live facade union finds exactly 665
source modules and 8,819 public declarations, with no missing module headers
or declaration doc comments. The reviewed 547-row source concordance is an
immutable merger ledger and remains 73 Lean-proved rows, 405 human-proved
frontier-result rows, 60 not-applicable rows, and 9 conjecture rows.

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
status ledger is 80 Exact, 86 Partial, 108 None, and 8 interface rows; the
191-result pre-Fabius core is 36/29/123/3. The compound outer spectral-product
theorem remains Partial even though the three-theorem outer-product leaf proves
local-uniform (normal) convergence for every complex strict contraction, its
nome-`1/4` Rvachev specialization, and the bounded-Fabius Fourier
specialization. Its named centered/MGF packaging and exterior reciprocal
formula, pole divisor, and zero--pole exchange remain outside Lean.

The merged q-series surface includes `RvachevPochhammerFactorization` (one
definition and ten theorems), `QPochhammerEntire` (zero definitions and five
legacy compatibility theorems), `QPochhammerInfinite` (one definition and
twenty-nine theorems), `QPochhammerDissection` (zero definitions and two
theorems), and `GeometricPochhammerNormalConvergence` (zero definitions and
three theorems). The public
`complexQPochhammerInf_eq_qPochhammerInfIn` bridge is unconditional. The
generic `analyticOrderAt_qPochhammerInfIn_of_eq_zero` theorem lives in
`QPochhammerInfinite`, requires exactly `‖q‖ < 1` and a zero hypothesis, and
includes `q = 0`; it is not duplicated in `QPochhammerEntire`.

The finite and analytic q-series crosswalk also includes
`GaussianBinomialContinuity` (three theorems), `JacobiTripleProduct` (two
definitions and twenty-five theorems), `QBinomialTheoremInfinite` (one
definition and twenty-two theorems), `QPascalSummation` (four theorems),
`QuantumBinomial` (two theorems), and `RogersSzegoPolynomial` (one definition
and nine theorems). `finiteQPochhammerIn_zero_left` remains uniquely owned by
`GaussianBinomialAtOne` and is only imported by
`QBinomialTheoremInfinite`.

The wider inventory includes `QPochhammerInfiniteBounds` (zero definitions
and five theorems), `QPochhammerComplexOrder` (one definition and four
theorems), `HeineTransformation` (two definitions and five theorems), and
`QGaussSummation` (zero definitions and two theorems), as well as the expanded
Euler, Jacobi, and Rogers--Szegő surfaces recorded declaration by declaration
in the master.

The q-calculus tranche comprises `LambertSeriesLog` (four theorems),
`PolynomialQDerivative` (two definitions and seventeen theorems),
`PolynomialQLeibniz` (four theorems), `QGamma` (two definitions and ten
theorems), and `QPochhammerDerivative` (three theorems). The exact-promotion
tranche comprises `QPochhammerIntegerIndex` (two definitions and fourteen
theorems), `ClassicalPochhammerLimit` (five theorems),
`GaussianBinomialUniversal` (two theorems), `PolynomialQTaylor` (two
definitions and fifteen theorems), and `QPartialFractions` (one definition
and five theorems).

The latest 37c q-series additions are `BasicHypergeometricSeries` (two
definitions and five theorems) and `QMultinomial` (one definition and nine
theorems). The former supplies uniform term bounds and the formalized
convergence half of the basic-hypergeometric classification; the latter gives
the Gaussian-product definition, functorial universal-polynomial form, and
division-free and quotient factorial identities.

The incoming eight-module union adds 58 public declarations:
`GaussianBinomialPalindromic` (zero definitions and twelve theorems),
`JacksonIntegral` (one definition and seven theorems), `QExponential` (three
definitions and eight theorems), `ThetaQuasiPeriodicity` (one definition and
six theorems), `JacobiCubic` (zero definitions and two theorems),
`QPochhammerLogDerivative` (zero definitions and ten theorems),
`QPochhammerOrderDerivative` (zero definitions and three theorems), and
`GaussianBinomialPolynomialStructure` (zero definitions and five theorems).
The two-module tail adds `CentralQBinomialReduction` (zero definitions and six
theorems) and `CyclotomicFactorization` (zero definitions and seven theorems).
The former proves the central base-\(q^2\) reduction both division-free over
every commutative ring and as a field quotient under the displayed
nonvanishing hypotheses. The latter proves the universal shifted-factorial
cyclotomic product over every commutative ring and the Gaussian cyclotomic
product over every integral domain, together with the exponent bounds.

The six-module aed union contributes exactly 50 public declarations. Its
complete surfaces and boundaries are:

- `PrimitiveRootBlock` (zero definitions, three theorems):
  `gaussianBinomial_isPrimitiveRoot_eq_zero`,
  `neg_one_pow_mul_pow_choose_two`, and
  `finiteQPochhammerIn_isPrimitiveRoot`. They work over a commutative integral
  domain; the first assumes a primitive root and `0 < k < d`, while the phase
  and block identities assume `0 < d`. The block theorem gives
  `∏ j<d, (1-y*ζ^j) = 1-y^d`, hence the manuscript's plus-sign form after
  `y=-x`.

- `QLucas` (zero definitions, eight theorems): `two_mul_choose_two`,
  `add_mul_add_sub_one`, `choose_two_add`,
  `coeff_finiteQPochhammerIn_neg_X`, `finiteQPochhammerIn_neg_X_block`,
  `coeff_block_pow_mul`, `pow_choose_two_add_mul_eq`, and
  `gaussianBinomial_q_lucas`. The first three are natural-number identities;
  the coefficient lemmas need only a commutative ring; the primitive-root
  results use a commutative integral domain, `0 < d`, and the displayed
  residue bounds. The terminal theorem proves only the evaluated identity
  `[ad+b,rd+s]_ζ = choose(a,r)*[b,s]_ζ`. It does not formalize the polynomial
  congruence modulo `Φ_d`, so `thm:q-lucas` is Partial.

- `CyclotomicDivisibility` (zero definitions, three theorems):
  `cyclotomic_exponent_eq_one_iff`,
  `cyclotomic_dvd_gaussianBinomial_iff`, and
  `gaussianBinomial_mul_isPrimitiveRoot`. The first two assume `k ≤ n` and
  `0 < d`, with the divisibility equivalence stated literally in `ℚ[X]`.
  The last assumes `0 < n` and a primitive root in a commutative integral
  domain; it proves the value clause but not the derivative clause of the
  Babbage corollary.

- `QCatalan` (one definition, eleven theorems): `qCatalan`; `map_qInt`,
  `qInt_X_monic`, `qInt_X_natDegree`, `X_sub_one_mul_qInt`,
  `qInt_X_eq_prod_cyclotomic`, `qInt_X_dvd_gaussianBinomial_rat`,
  `qInt_X_dvd_gaussianBinomial_int`, `qInt_X_mul_qCatalan`,
  `qCatalan_natDegree`, `qCatalan_eval_one_mul`, and `qCatalan_eval_one`.
  These give the exact quotient in `ℤ[X]`, its degree and value at one for
  every natural `n`; they make no coefficient-positivity claim.

- `NewtonInterpolation` (two definitions, thirteen theorems): `newtonCoeff`,
  `newtonInterpolant`; `newtonCoeff_eq`, `newtonCoeff_zero`,
  `newtonCoeff_mul_prod`, `newtonPoly_succ`, `eval_newtonPoly`,
  `degree_newtonPoly_lt`, `newtonPoly_eq_interpolate`,
  `eq_newtonPoly_of_eval_eq`, `coeff_newtonPoly_self`,
  `newtonCoeff_eq_sum`, `nodal_range_pow`, `prod_erase_pow_sub_pow`, and
  `newtonCoeff_pow_eq_sum`. All are finite algebra over an arbitrary field.
  Evaluation needs the prefix product nonzero; interpolation and coefficient
  formulas use finite-range injectivity; the geometric basis needs `q ≠ 0`,
  and its denominator identity needs only `j ≤ k`. No infinite-series claim
  is made. The `newtonInterpolant` rename preserves the established,
  scalar-sequence `Fabius.newtonPoly` API; theorem compatibility names remain
  unchanged.

- `QBetaIntegral` (one definition, eight theorems): `qBeta`; `qNumber_pos`,
  `qBeta_term_eq`, `qBeta_eq_prod`, `qBeta_eq_qGamma`, `qBeta_comm`,
  `qBeta_pos`, `qBeta_add_one_left`, and `qBeta_add_one_right`. The definition
  is total on real parameters. The term identity assumes `0 < q < 1` and
  `y > 0`, with arbitrary real `x`; the evaluations, symmetry, positivity,
  and recurrences assume exactly `0 < q < 1` and `x,y > 0`. No complex
  continuation or classical-limit theorem is claimed.

The master contains an exhaustive declaration-by-declaration crosswalk for
these six modules together with the prior ten-module tail. Its 282-row
forward ledger is 80 Exact, 86 Partial, 108 None, and 8 interface rows.
`lem:central-reduction` and `thm:cyclotomic-pochhammer` remain Exact. In
particular, `thm:qbinom-structure` is Exact and `thm:qbinom-moments` is
Partial: palindromicity proves the mean identity, but the variance clause
remains outside Lean. The half-base Gaussian valuation row also remains
Partial: Lean proves the reciprocal identity and symmetry used in the
argument, but not its concluding odd-integer valuation statement.

The live master and retained PDF are not synchronized after the aed source
integration. The partial root `SHA256SUMS` intentionally records only stable
or historical hash-valid payloads. A fresh publication build and exhaustive
ledger regeneration are required before release parity may be claimed.
