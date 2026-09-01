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

The retained `q_pochhammer_q_binomial_monograph.pdf` is a 340-page A4
historical checkpoint built from the then-current source (13,690 lines,
628,147 bytes, SHA-256
`da420f5b2622cd088af43cea0ac448105c9f6af65cf1734de6535e3427f8e052`).
The PDF is 2,180,191 bytes with SHA-256
`e64a4ef65a9fcce3a4f211f2125b0f8440910cf4527635f76975b0967800e667`.
That checkpoint was built by exactly three guarded, serial
`pdflatex -interaction=nonstopmode -halt-on-error` passes, which produced 331,
340, and 340 pages. The inputs were unchanged before and after each pass, and
no TeX, Lean, or Lake work interleaved with them. The final log scan found zero
overfull boxes. All 340 pages are text-bearing, and all 1,700
MediaBox/CropBox/BleedBox/TrimBox/ArtBox values match A4 exactly. `pdffonts`
reports 42 of 42 Type-1 font rows embedded and subsetted, including five
Libertinus rows, with no Type-3 font. Fresh full-page visual inspection of
physical pages 1, 247, 313, 314, 319, 338, and 340 was clean. The files under
`assets/experiments/**/figures/` remain research figures, not publication
manuscripts.

The live source now includes exhaustive crosswalks for
`QPochhammerEntire` (four legacy compatibility wrappers),
`QPochhammerInfinite` (one definition and twenty-nine theorems), and
`QPochhammerDissection` (two theorems), together with expanded Euler,
infinite-q-binomial, Jacobi, and Rogers--Szegő material.  The two newest
generic theorems are
`deriv_qPochhammerInfIn_ne_zero_of_mul_pow_eq_one`, which gives a nonzero
derivative at every raw factor zero `a*q^j = 1` including `q = 0`, and
`analyticOrderAt_qPochhammerInfIn_of_eq_zero`, which gives analytic order
exactly one at every zero.  The unchanged `QPochhammerEntire` declarations
retain the older `complexQPochhammerInf` names by transferring these generic
facts, not by duplicating their analytic proofs.  `QBinomialTheoremInfinite`
has one definition and twenty-two theorems; `finiteQPochhammerIn_zero_left`
is canonically declared in `GaussianBinomialAtOne` and is only imported there,
not redeclared.
Those post-checkpoint source changes mean that the retained PDF does not render
the live source. Publication synchronization requires a fresh exact three-pass
build followed by regeneration of the root package checksum ledger.
