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

The retained canonical publication artifact is
`q_pochhammer_q_binomial_monograph.pdf`. It was built from the then-current
source SHA-256
`9b7ac11a815efa7f3c6ea08b9626c06143fd6b0d633fef6edfc8bc21c2f6783a`,
with `origin/main` pinned at
`8a7d03dc379638a6cbda302074b2feba27c21961` when the gate began, by exactly
three successful consecutive serial
`pdflatex -interaction=nonstopmode -halt-on-error` passes with
`SOURCE_DATE_EPOCH=1788242400`. The final pass produced a 335-page A4 PDF of
2,163,339 bytes with SHA-256
`91c649d0c69628e134e71f1be6c39c3cbc96b91bfc63e456011083cf0e882f03`.
The final log has no layout, reference, rerun, font, package, or PDF-string
warning. `pdfinfo` reports A4 media and zero rotation on every page.
`pdffonts` reports 42 Type-1 entries, all embedded and subsetted, including
five Libertinus entries and no Type-3 font. Poppler rendered all 335 pages at
298-by-421 pixels without a blank page. Every page was covered by nine complete
contact sheets; pages 1, 115, 263, 284, 308, 329, and 335 were additionally
inspected at 1,191-by-1,684 pixels, covering the title, both exact
`q=-1` crosswalks, the certification chapter, the formalization appendix, its
final register page, and the end of the index. The files under
`assets/experiments/**/figures/` remain research figures, not publication
manuscripts.

The current master TeX is a source-only successor to that checkpoint. Its
13,914-line, 646,156-byte source has SHA-256
`bf270b5f522b159576d91121110239bdf6797640e1ac307111a1895ac0c70109`.
It includes exhaustive crosswalks for `QPochhammerEntire` (zero definitions
and five theorems), `QPochhammerInfinite` (one definition and twenty-seven
theorems), and `QPochhammerDissection` (zero definitions and two theorems).
The `QPochhammerEntire` crosswalk records fixed-nome local uniformity and
entireness, the division-free factor-zero criterion valid at `q = 0`, the
reciprocal-power zero lattice for nonzero nome, and simple analytic order at
every zero. The forward status ledger is 48 Exact, 77 Partial, 149 None, and
8 interface rows; the 190-result pre-Fabius core is 42/33/112/3, and its
q-shifted-factorial chapter is 6/1/8/0. The compound outer spectral-product
theorem remains Partial: local uniformity for one symbol as a function of its
argument at fixed contracting nome does not establish normal convergence of
the additional product over spectral scales.

No PDF was rebuilt for this source-only update. The retained 335-page PDF is
therefore a historical publication checkpoint, and exact source/PDF parity is
not claimed.
