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

The retained `q_pochhammer_q_binomial_monograph.pdf` is a 348-page A4
build of the current master source (14,158 lines, 661,835 bytes,
SHA-256 `79ee5e60a6c7e42a91c58dcd9bcae56173cc6b4aa3e54739a461943f705f3904`).
The PDF is 3,002,729 bytes with SHA-256
`8bf14b52d8a0fc0abc4d54cca503fd47a2df37cf76ee1bb4e442bea1fd2a4aa7`.
It was built by exactly three serial
`pdflatex -interaction=nonstopmode -halt-on-error` passes, which produced 338,
348, and 348 pages, with `makeindex` run on the `.idx` file after each pass.
The final log scan found three overfull boxes, all in the single paragraph of the QPochhammerEntire crosswalk (source lines 652--670) whose long declaration names lack break points. All pages are A4. `pdffonts` reports 42 font rows, all
embedded and subsetted, including 5 Libertinus rows, with no Type-3
fonts. The files under `assets/experiments/**/figures/` remain research
figures, not publication manuscripts.

The master source is the one described above. Its
14,088-line, 657,425-byte source has SHA-256
`791152ff41477e4f187d18edab195f1aa1232e9fbcafbbd536a62b24a7b8e799`.
It includes exhaustive crosswalks for `QPochhammerEntire` (zero definitions
and five legacy compatibility theorems), `QPochhammerInfinite` (one definition
and twenty-nine theorems), `QPochhammerDissection` (zero definitions and two
theorems), and `QBinomialTheoremInfinite` (one definition and twenty-two
theorems), together with `GeometricPochhammerNormalConvergence` (zero
definitions and three theorems). The newer inventory also includes
`QMultinomial` (one definition and seven theorems),
`QPochhammerInfiniteBounds` (five theorems), `QPochhammerComplexOrder` (one
definition and four theorems), `BasicHypergeometricSeries` (two definitions
and five theorems), `HeineTransformation` (two definitions and five theorems),
and `QGaussSummation` (two theorems), as well as expanded Euler, Jacobi, and
Rogers--Szegő material.
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
status ledger is 73 Exact, 84 Partial, 117 None, and 8 interface rows; the
191-result pre-Fabius core is 36/29/123/3. The compound outer spectral-product
theorem remains Partial even though the three-theorem outer-product leaf proves
local-uniform (normal) convergence for every complex strict contraction, its
nome-`1/4` Rvachev specialization, and the bounded-Fabius Fourier
specialization. Its named centered/MGF packaging and exterior reciprocal
formula, pole divisor, and zero--pole exchange remain outside Lean.

No PDF was generated for this source-only crosswalk update. The 347-page PDF
therefore remains a source-pinned historical artifact, while the root package
checksum ledger records the live source and retained PDF as distinct payloads.
PDFs are rebuilt in batches, at most about once per hour; synchronization is
claimed only after a fresh guarded build.
