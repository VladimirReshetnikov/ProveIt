# Validation record

This record separates completed inventory and publication checks from the
remaining fresh-checkout and full numerical reproducibility work. The
immutable source baseline is
`73f0b373126ef22a3b5dccadfa7b99d61d445345`.

## Completed source and evidence checks

- The source-pin subtree contains exactly 180 files: 179 under the four pre-
  synthesis report trees and their parent routing README.
  `../source_disposition.csv` assigns every source file a canonical disposition.
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
- `../post_pin_disposition.csv` accounts for all 15 paths added and eight paths
  modified between the immutable source pin and that reconciliation revision,
  including the two retained environment files.

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
  800 labels, 769 references, 62 bibliography keys, the 180-row source
  disposition, the 23-row post-pin reconciliation, the 151-row historical-
  ledger audit, 111 companion-payload provenance rows for 110 physical
  payloads, the exhaustive root checksum ledger, and the 232-row theorem
  concordance. The concordance source projection is
  `a065b161c80786829033f1efd39bb5d1e4c521b9b9c4446959a73729a55718e0`.
- The validator's Lean check is intentionally narrow: it confirms that the
  curated declaration name occurs in its nominated module. It does not invoke
  Lean, compare theorem types, or claim that the one curated row is a complete
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
  including the complete evidence tree, without duplicate or stale paths, and
  verifies in full. The eight historical source-package ledgers summarized by
  the audit remain unchanged and are not live manifests.

## Reproducibility work not rerun

The publication build did not rerun every retained numerical script, and the
complete gate has not yet been reproduced from a fresh checkout. These are
independent reproducibility tasks, not missing PDF-validation steps. Passing a
Python syntax check, finding an old PDF, or matching a historical checksum
still does not certify a numerical replay.

## Recorded provenance limitation

The provenance chapter's statement that the nine predecessor packages retain
"theorem-level mapping" in the current concordance is too strong. The 232-row
concordance begins with the four peer manuscripts; the earlier nine packages
retain original bytes, source-hash prefixes, and package-level contribution
summaries, not a second theorem-by-theorem concordance. The accurate scope is
recorded in `../PROVENANCE.md`. Correcting the TeX sentence requires a paired
PDF rebuild, which was deliberately skipped at the user's direction; neither
the source nor the PDF was changed in this source-neutral consolidation pass.

## Required publication procedure

After the final TeX edit, use the exact three-pass command sequence in the
canonical README's [build section](../README.md#build-the-canonical-article).
Then inspect the final log for errors, unresolved references, rerun requests,
and overfull boxes; inspect PDF metadata and fonts; render every page; and
visually examine every rendered page. The measured result of that procedure is
recorded above.
