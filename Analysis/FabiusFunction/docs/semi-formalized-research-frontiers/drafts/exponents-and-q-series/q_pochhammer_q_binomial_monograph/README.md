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
environments a reviewed disposition. With the current exact promotions, the
canonical-status totals are 73 Lean-proved rows, 405 human-proved frontier
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

The final release-checksum gate is:

```text
python audit/build_package_checksums.py --check
```

It checks every permanent package file except the self-referential root
`SHA256SUMS` ledger itself. The regenerated root ledger is exhaustive: all 70
permanent package paths are covered, and the check above passes. The nested
asset ledger remains independently useful because it preserves the migrated
experiment and research-figure boundary.

The current `q_pochhammer_q_binomial_monograph.pdf` is the synchronized
357-page A4 publication. Its final 14,635-line, 688,123-byte master source has
SHA-256
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

Before the build, both the local remote-tracking ref and remote
`origin/main` were pinned to
`5e3fe8fcb99d0662096fe39c436d51a6ec7c1169`; the clean working HEAD
`191cce0e849a330f173c25be2b9f2f4cd7c2f211` had that checkpoint as a merge
parent. The mandatory post-build check observed that `origin/main` had moved
to `e6f3308dc377baa46aaa9463f0ae6fe9451d5ee2`. This receipt therefore attests
the exact source/PDF hashes above; later upstream q-source edits require a new
build after they are integrated. Files under `assets/experiments/**/figures/`
remain research figures rather than publication manuscripts.

An independent lexical audit of the live facade union finds exactly 659
source modules and 8,769 public declarations, with no missing module headers
or declaration doc comments. The reviewed 547-row source concordance records
73 Lean-proved rows, 405 human-proved frontier-result rows, 60 not-applicable
rows, and 9 conjecture rows.

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

The master contains an exhaustive declaration-by-declaration crosswalk for
all ten modules. Its 282-row forward ledger is 73 Exact, 84 Partial, 117 None,
and 8 interface rows: `lem:central-reduction` and
`thm:cyclotomic-pochhammer` are the two new Exact promotions. In particular,
`thm:qbinom-structure` is Exact and
`thm:qbinom-moments` is Partial: palindromicity proves the mean identity, but
the variance clause remains outside Lean. The half-base Gaussian valuation row
also remains Partial: Lean proves the reciprocal identity and symmetry used in
the argument, but not its concluding odd-integer valuation statement.

The checked master and PDF are synchronized at the source and artifact hashes
recorded above. The exhaustive root `SHA256SUMS` verifies every permanent
package payload; any later source change invalidates this receipt and requires
a fresh publication build and ledger regeneration.
