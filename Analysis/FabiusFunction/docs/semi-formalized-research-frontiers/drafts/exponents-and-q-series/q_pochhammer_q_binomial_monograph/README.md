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

The retained publication artifact is `q_pochhammer_q_binomial_monograph.pdf`.
It was built from its publication-checkpoint source by three consecutive serial
`pdflatex -interaction=nonstopmode -halt-on-error` passes with
`SOURCE_DATE_EPOCH=1788242400`; all three passes produced the same bytes. The
result is a 334-page A4 PDF of 2,917,795 bytes with SHA-256
`aa75c32926fb0d5b20d831f9df0be584073f1cbc4232c25facbd21d98b9f680d`.
The final log has no layout, reference, rerun, font, package, or PDF-string
warning. `pdffonts` reports every font embedded and subsetted, including the
Libertinus serif and monospaced faces. Poppler rendered all 334 pages at
827-by-1170 pixels. Every page was covered by the complete contact-sheet
review; the six pages changed during the final typography repair were also
inspected at full resolution, while the remaining 328 renders were
byte-identical to their already reviewed versions. The files under
`assets/experiments/**/figures/` remain research figures, not publication
manuscripts.

The current master TeX is a source-only successor to that checkpoint.  It
contains later notation repairs and the exact five-theorem
`FabiusFunction.QPochhammerEntire` crosswalk: fixed-nome local uniformity and
entireness, both division-free and reciprocal-power zero descriptions, and
simple analytic order at every zero.  Consequently the retained 334-page PDF
is historical and exact source/PDF parity is not claimed; no PDF was rebuilt
for this tranche.  The forward status ledger is now 42 Exact, 73 Partial, 159
None, and 8 interface rows.  The 190-result pre-Fabius core is 36/29/122/3,
and its q-shifted-factorial chapter is 4/1/10/0.  The compound outer
spectral-product theorem remains Partial: the new locally uniform theorem
concerns one symbol as a function of its argument at fixed contracting nome,
not normal convergence of the additional product over spectral scales.
