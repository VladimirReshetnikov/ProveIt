# Validation record

This record separates completed inventory and canonical-publication checks
from outstanding reproducibility work. The immutable source baseline is
`73f0b373126ef22a3b5dccadfa7b99d61d445345`; full numerical replay and
fresh-checkout reproduction remain separate.

After the incoming publication checkpoint, the Lean crosswalk for
`thm:weight-valuation` updated `chapters/03_additive_dyadic.tex` and the theorem
concordance. The live q-series master was later renamed, so
`chapters/01_geometric_core.tex` and `chapters/99_bibliography.tex` were updated
to its stable publication path. The current PDF was rebuilt after those edits
and is synchronized with the current chapter bytes.

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

## Current synchronized publication checkpoint

- Exactly three strict serial pdfLaTeX passes were run after the final path
  edits with `SOURCE_DATE_EPOCH=1788242400`. The first pass refreshed the
  cross-reference state; passes two and three were byte-identical, each writing
  the final 2,934,621-byte artifact with SHA-256
  `00070eafd0734681a7dd125cb64e4c898710c01dc8c8220362550567843bce00`.
- The current PDF has 156 pages. Every page is A4 (595.276 by 841.89 points),
  has rotation zero, and contains extractable text. The PDF is readable,
  unencrypted version 1.5 with no JavaScript or structural suspect flag.
- All 33 font rows are embedded and subset Type 1 faces; seven are Libertinus
  and none is Type 3.
- The final log has no TeX error, undefined reference or citation, rerun
  request, duplicate destination, or overfull box. Its 36 package warnings
  (24 hyperref, 11 caption, and one amsmath) and six underfull boxes are the
  same benign classes documented at the incoming checkpoint.
- Poppler rendered all 156 pages. Six complete contact sheets were reviewed;
  pages 10, 125, 155, and 156 were additionally inspected at full resolution
  because they contain the renamed master reference, the valuation crosswalk,
  or the updated bibliography URL. No clipping, overlap, corrupt image,
  missing glyph, or unintended blank page was found.

## Historical incoming publication-artifact gates

- `python audit/validate_canonical.py` passes the canonical nine-file TeX
  graph, environment balance, 212 result environments (149 proof-required),
  800 labels, 781 references, 62 bibliography keys, the 180-row source
  disposition, the 23-row post-pin reconciliation, the 151-row historical-
  ledger audit, 111 companion-payload provenance rows for 110 physical
  payloads, the exhaustive root checksum ledger, and the 232-row theorem
  concordance. The concordance source projection is
  `a065b161c80786829033f1efd39bb5d1e4c521b9b9c4446959a73729a55718e0`.
- The validator's Lean check is intentionally narrow: it confirms that the
  curated exact and partial-support declaration names occur in their nominated
  modules. It does not invoke Lean, compare theorem types, or claim that the
  three exact concordance rows are a complete census of current formal results.
  Generic decoder synthesis, node biorthogonality, coefficient factorization,
  the full interpolation loop, and the unnormalized decoder row-sum law are
  checked at this identifier level. The geometric Gaussian closed-form
  decoder, its elementary-symmetric/prefactor formula, a typed `Matrix`
  wrapper, and optimization are not claimed. The exact
  `Fabius.twoPowChoose_padicValNat` crosswalk covers only the strict-interior
  dyadic valuation formula; the separately stated endpoint-flat companion
  assertion remains unformalized.
- The publication driver itself remains at 188 lines, 6,722 bytes, and SHA-256
  `92878edbef877a5e121c96cc80a003bd2137150550c8e05b5cd970ecefe6b248`.
  At the incoming artifact's build checkpoint, the driver, its seven included
  chapters, and the shared notation file had the fixed combined SHA-256
  `941950f6416e8087b209c6c2af596343daca3881c11d44694b1cbc75d3dbe97a`
  throughout the final build cycle.
- After a separate empty-TeX-lane and clean-auxiliary gate, exactly three
  strict, uninterrupted serial pdfLaTeX passes were run from that frozen
  source. All three exited successfully, no other TeX process appeared between
  passes, and no later TeX pass was run. The successive pass products had 149,
  156, and 156 pages; the final pass wrote 2,452,884 bytes.
- The retained incoming publication PDF has 156 pages, 2,452,884 bytes, and
  SHA-256
  `ea23b4ad19a41c5246b548db7c79e18d50835b697a88e9a5aa2b1188af3b4d35`.
  Every page is 595.276 by 841.89 points (A4), has
  rotation zero and identical MediaBox, CropBox, BleedBox, TrimBox, and ArtBox
  values, and contains extractable text.
- All 33 font rows are embedded and subset Type 1 faces; seven are Libertinus
  and none is Type 3. The document is readable, unencrypted PDF 1.5 with
  populated title, subject, and keyword metadata, no JavaScript, and no PDF
  structural suspect flag.
- The final-pass log contains no TeX error, undefined reference or citation,
  rerun request, duplicate destination, or overfull box. It contains 36 benign
  package warnings (24 hyperref, 11 caption, and one amsmath) and six
  underfull boxes; all affected layouts were included in the visual review.
- All 156 pages were rendered and reviewed in six contact sheets. Pages 1, 10,
  37, 38, 45, 149, 150, and 156 were additionally inspected at full size; no
  clipping, overlap, corrupt image, missing glyph, or unintended blank page
  was found.
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
recorded in `../PROVENANCE.md`. This path-maintenance rebuild deliberately
leaves that separate wording limitation unchanged in both source and PDF.

## Required publication procedure

After the final TeX edit, use the exact three-pass command sequence in the
canonical README's [build section](../README.md#build-the-canonical-article).
Then inspect the final log for errors, unresolved references, rerun requests,
and overfull boxes; inspect PDF metadata and fonts; render every page; and
visually examine every rendered page. The current synchronized result of that
procedure is recorded above; the earlier incoming-artifact measurements remain
below as historical provenance.
