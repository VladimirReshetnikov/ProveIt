# q-Series and inverse q-analogs

This directory contains the one canonical document for forward q-series and
branch-aware inverse q-analog theory:
`q_series_and_inverse_analogs.tex`. Files under `chapters/` are implementation
units included by that master; they are not independent manuscripts.

The consolidation uses the former q-Pochhammer/q-binomial monograph as its
forward backbone and incorporates the former inverse-q synthesis as a
specialist part. The three general q-series guides are donor manuscripts:
their repeated results map to one strongest canonical statement, while only
genuinely stronger or independent material is transplanted. They remain in
the feature branch only until the new five-publication source concordance has
assigned every result environment a reviewed disposition.

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
are immutable. `audit/MERGE_SOURCE_REVISION` pins the five live publications
that are being merged here at commit
`9560165ae2eb33590404a090ab26bd3ca715f32f`. A separate source concordance
will cover that 547-environment merge surface rather than overloading the old
inverse-q ledger.

The migrated `assets/` tree preserves six experiment programs, nineteen
CSV/TXT outputs, and fourteen vector figures selected by the historical
77-row `assets/ASSET_DISPOSITION.csv`. Its active `assets/SHA256SUMS` has 43
entries because it also covers asset metadata and environment files; this is
not a contradiction with the 39 retained historical payloads.

## Validation state

The source-only structural gate is:

```text
python audit/validate_canonical.py
```

It checks the complete input graph, balanced environments, unique labels,
resolved references, proof coverage, the 260-row inverse concordance, and
reproduction of the pinned six-package source inventory. A second audit lane
will validate the five-publication source concordance before retirement of the
donor packages.

There is intentionally no canonical PDF in this directory. PDF generation
was skipped by explicit user direction, and the two superseded publication
PDFs were deleted rather than renamed into a misleading partial rendering.
The PDF files under `assets/experiments/**/figures/` are retained research
figures, not publication manuscripts. No current claim is made about TeX
compilation, page count, font embedding, or rendered-page inspection.
