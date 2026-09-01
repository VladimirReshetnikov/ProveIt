# Validation record

This record deliberately distinguishes completed inventory and canonical-
publication work from outstanding reproducibility work. The structural
validator, final PDF, and live root/asset ledgers were complete at this
recorded checkpoint; full numerical replay and fresh-checkout reproduction
remain separate. The immutable source baseline is
`73f0b373126ef22a3b5dccadfa7b99d61d445345`.

After that publication checkpoint, the source-only Lean crosswalk for
`thm:weight-valuation` updated `chapters/03_additive_dyadic.tex` and the
theorem concordance.  The canonical validator and live ledgers were refreshed,
but the PDF was intentionally not rebuilt.  Consequently the PDF measurements
below are historical validation of the retained artifact, not a claim that it
renders the current chapter bytes.

## Completed source and evidence checks

- The four pre-synthesis report trees contain exactly 180 files at the source
  pin, and `../source_disposition.csv` assigns every source file a canonical
  disposition.
- The former additive-dyadic volume's provenance appendix explicitly accounts
  for all nine nested manuscript packages. Their duplicated documentation was
  therefore eligible for retirement after its content was absorbed.
- The three geometric manuscripts are distinct sources, not byte duplicates;
  their common material is editorially deduplicated and their unique material
  is routed into the canonical chapters.
- The only byte-identical source-payload pair is the two-line requirements file
  shared by two interpolation packages. It is retained once under
  `companion-evidence/shared/` while both source rows remain in the disposition
  ledger.
- All 13 retained Python scripts passed a syntax parse during the asset audit.
- All 20 PNG files present at the source pin passed structural image inspection
  during the asset audit.
- A figure-only replay of
  `fabius_interpolation_report/numerical_experiments.py` supplied three missing
  PNG companions, bringing the current companion-evidence tree to 23 PNG
  files. This was a targeted figure repair, not a full numerical replay of all
  packages.
- Mainline reconciliation retained the arbitrary-ratio report's exact direct
  requirements and 12-package lock.  Both files are checked against revision
  `9e70a1a2145e9c01566d5638d33045af24516790` and are deliberately separate
  from the 180-file source-pin disposition.

## Historical-ledger audit

The eight retired package ledgers contribute 151 rows. Recalculation at the
source pin classified them as follows:

| Result | Rows |
| --- | ---: |
| exact byte match | 68 |
| match after CRLF/LF normalization | 34 |
| substantive mismatch | 29 |
| referenced path missing | 20 |

The complete row-level audit is
[`HISTORICAL_LEDGER_AUDIT.csv`](HISTORICAL_LEDGER_AUDIT.csv). Because these
are historical manifests, mismatches are reported rather than silently
rewritten. They do not certify the current canonical payloads.

## Completed canonical publication gates

- `python audit/validate_canonical.py` passes the canonical nine-file TeX
  graph, environment balance, 212 result environments (149 proof-required),
  800 labels, 770 references, 62 bibliography keys, the 180-row source
  disposition, the 151-row historical-ledger audit, 111 companion-payload
  provenance rows for 110 physical payloads and 114 live asset hashes, and the
  232-row theorem concordance. The concordance source projection is
  `a065b161c80786829033f1efd39bb5d1e4c521b9b9c4446959a73729a55718e0`.
- The validator's Lean check is intentionally narrow: it confirms that the
  curated declaration name occurs in its nominated module. It does not invoke
  Lean, compare theorem types, or claim that the two curated rows are a complete
  census of current formal results.
- The final source has 188 lines, 6,722 bytes, and SHA-256
  `92878edbef877a5e121c96cc80a003bd2137150550c8e05b5cd970ecefe6b248`.
- Exactly three strict, serial pdfLaTeX passes were run from the final source.
  All three exited successfully; no later TeX pass was run.
- The final PDF has 155 pages, 2,448,906 bytes, and SHA-256
  `d1f89b005bcae9afc9c70b4ccce632aa8c665ed68e98bacb2ff96827dd427095`.
  Every page is 595.276 by 841.89 points (A4), has rotation zero and identical
  MediaBox, CropBox, BleedBox, TrimBox, and ArtBox values, and contains
  extractable text.
- All 33 PDF font rows are embedded and subset; seven are Libertinus and none
  is Type 3. The document is readable, unencrypted PDF 1.5 with populated
  title, subject, and keyword metadata.
- The final log contains no TeX error, undefined reference or citation, rerun
  request, duplicate destination, or overfull box. It contains 36 benign
  package warnings (24 hyperref, 11 caption, and one amsmath) and six
  underfull boxes; all affected layouts were included in the visual review.
- All 155 pages were rendered and reviewed in five contact sheets. Pages 1,
  91, 109, 145, and 155 were additionally inspected at full size; no clipping,
  overlap, corrupt image, or unintended blank page was found.
- The root `SHA256SUMS` exhaustively covers every other permanent package file,
  without duplicate or stale paths, and verifies in full. The dedicated live
  `assets/SHA256SUMS` likewise verifies the current evidence tree; the eight
  historical source-package ledgers summarized by the audit remain unchanged.

## Reproducibility work not rerun

The publication build did not rerun every retained numerical script, and the
complete gate has not yet been reproduced from a fresh checkout. These are
independent reproducibility tasks, not missing PDF-validation steps. Passing a
Python syntax check, finding an old PDF, or matching a historical checksum
still does not certify a numerical replay.

## Required publication procedure

After the final TeX edit, run exactly three strict serial passes from the
canonical package root:

```text
pdflatex -interaction=nonstopmode -halt-on-error comb_interpolation_synthesis.tex
pdflatex -interaction=nonstopmode -halt-on-error comb_interpolation_synthesis.tex
pdflatex -interaction=nonstopmode -halt-on-error comb_interpolation_synthesis.tex
```

Then inspect the final log for errors, unresolved references, rerun requests,
and overfull boxes; inspect PDF metadata and fonts; render every page; and
visually examine every rendered page. The measured result of that procedure is
recorded above.
