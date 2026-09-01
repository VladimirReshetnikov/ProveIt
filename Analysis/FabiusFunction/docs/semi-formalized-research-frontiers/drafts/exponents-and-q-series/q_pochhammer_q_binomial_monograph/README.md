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
canonical-status totals are 70 Lean-proved rows, 408 human-proved frontier
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

The exhaustive package checksum gate is:

```text
python audit/build_package_checksums.py --check
```

It checks every permanent package file except the self-referential root
`SHA256SUMS` ledger itself. The nested asset ledger remains independently
useful because it preserves the migrated experiment and research-figure
boundary.

The retained `q_pochhammer_q_binomial_monograph.pdf` is a 347-page A4
publication checkpoint. It was built from a 14,072-line, 656,200-byte master
with SHA-256
`062b7230d95ff8bd52b11253c6c3c8820d6f6a82e4307ae5d82a1d793c00c517`.
The PDF is 2,996,319 bytes with SHA-256
`29b422a39c42be37bd1487d4245c44e55706720c545dd015957644e47014bd48`.
Exactly three serial
`pdflatex -interaction=nonstopmode -halt-on-error` passes produced 337, 347,
and 347 pages, with `makeindex` run after each pass. The final log recorded
three overfull boxes in the long `QPochhammerEntire` crosswalk paragraph.
All pages are A4, and all 42 reported font rows are embedded and subsetted,
including five Libertinus rows, with no Type-3 font.

That PDF and source were synchronized at the named build checkpoint, but the
merged master now includes later API and crosswalk changes. The retained PDF
is therefore a verified historical artifact, not a render of the live TeX.
The earlier 345-page receipt (source SHA-256
`7389b325c08df9c731942b1f67b58511d1b7624a4b03153ee23fa3edcd9dcfa3`,
PDF SHA-256
`6d5477affdff8eb9711232c3ab7b1ad53dda3ad9a866e8fc031f5e787fcffc59`)
remains recorded in `PROVENANCE.md`. Files under
`assets/experiments/**/figures/` remain research figures rather than
publication manuscripts.

An independent lexical audit of the live facade union finds exactly 649
source modules and 8,698 public declarations, with no missing module headers
or declaration doc comments. The reviewed 547-row source concordance records
70 Lean-proved rows, 408 human-proved frontier-result rows, 60 not-applicable
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

The live master, this README, and the extractor postdate the retained PDF.
The root `SHA256SUMS` is intentionally a partial operational ledger: it
verifies stable payloads and the historical PDF only. A final source freeze,
fresh publication build, and full checksum regeneration are required before
source/PDF synchronization or a complete release ledger may be claimed.
