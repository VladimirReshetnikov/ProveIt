# Validation record

This record distinguishes completed inventory work, historical publication
checkpoints, and the current source graph. The immutable source
baseline is `73f0b373126ef22a3b5dccadfa7b99d61d445345`. Historical artifacts remain
receipts only for their stated input graphs. Full numerical replay and
fresh-checkout reproduction remain separate.

The current source combines the incoming stable-path revisions to
`chapters/01_geometric_core.tex` and `chapters/99_bibliography.tex` with the
local general-$q$/endpoint-jet, Lagrange,
`FabiusFunction.PrimePowerBinomialValuation`, reference-appendix, and driver
revisions in `chapters/03_additive_dyadic.tex`,
`chapters/90_reference_appendices.tex`, and
`comb_interpolation_synthesis.tex`, followed by the exact generic-prime and
dyadic companion-row valuation crosswalk.  A later source-only notation pass
also replaced the true two-adic valuation by `\TwoAdicValuation` and renamed
the geometric Newton coefficient family consistently across the driver,
chapter 01, and chapter 90 as
`\FabiusGeometricNewtonCoefficient{k}{q}`. The repository-wide documentation
census recorded at the earlier merge checkpoint was 629 Lean modules and 8,546
public declarations. The checked-in PDF was built from the earlier source graph
and passed the complete publication gate recorded below. Later
canonical-notation edits in chapters 01, 03, and 90 and in the driver require
a fresh exact three-pass render. Package checksum manifests are retired and no
longer participate in current validation. The retained PDF and current source
remain distinct payloads.

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

## Current source-only companion-row valuation checkpoint

- The current source-only notation layer uses
  `\FabiusGeometricNewtonCoefficient{k}{q}` for the Fabius divided-difference
  coefficient on the complete node list $1,q,\ldots,q^k$, including the
  $k=0$ boundary, and reserves `\TwoAdicValuation` for the actual dyadic
  valuation.  The retained PDF predates these notation-only edits.
- The existing strict-interior dyadic comb-weight theorem remains crosswalked
  exactly to `Fabius.twoPowChoose_padicValNat`; the arbitrary-prime row-$p^m$
  declarations and their positive right endpoint remain unchanged.
- The chapter now proves the stronger companion proposition.  For every prime
  $p$, all columns $0\le r<p^m$ in row $p^m-1$ are $p$-adic units, and for the
  essential strict range $0<j<p^m$,
  $v_p\binom{p^m-2}{j-1}=v_p(j)$.  Its exact compiled declaration crosswalk is
  `Fabius.primePowerSubOneChoose_padicValNat`,
  `Fabius.primePowerSubTwoChoose_padicValNat`, and
  `Fabius.twoPowSubTwoChoose_padicValNat`, respectively.  The last declaration
  is the dyadic specialization used for the endpoint-flat weights.
- The concordance generator checks all three new identifiers in
  `FabiusFunction.PrimePowerBinomialValuation` while preserving the existing
  `Fabius.twoPowChoose_padicValNat` declaration as the primary exact mapping
  for source row `thm:weight-valuation`.  The curated concordance remains 232
  rows with source projection
  `a065b161c80786829033f1efd39bb5d1e4c521b9b9c4446959a73729a55718e0`.
  This is an identifier-presence check, not a Lean build or theorem-type check.
- The source validator passes the nine-file TeX graph, environment and proof
  discipline (213 result environments, 150 proof-required), 801 labels, 783
  references, 62 bibliography keys, all disposition and evidence audits, the
  concordance, and the exhaustive package ledger.
- No PDF was rebuilt.  The retained 158-page PDF remains the validated
  historical checkpoint with 2,456,105 bytes and SHA-256
  `81d249c8b2bb124836c858bd8e0ef9c8764606a2f9655a798d69e7565b1759b4`;
  the root ledger records it separately from the current source.

## Retained semantic-union publication checkpoint

- The current union retains the incoming `chapters/01_geometric_core.tex` and
  `chapters/99_bibliography.tex` path corrections together with the local
  `chapters/03_additive_dyadic.tex`, `chapters/90_reference_appendices.tex`, and
  publication-driver revisions. In particular, it preserves the Lagrange
  synthesis facts and the exact strict-interior dyadic crosswalk to
  `Fabius.twoPowChoose_padicValNat`, plus the stronger arbitrary-prime results
  in `FabiusFunction.PrimePowerBinomialValuation`.
- The publication root began at branch HEAD
  `31cb348d53772f5e452794b2f62e2eca5782a285` with `origin/main` at
  `8a7d03dc379638a6cbda302074b2feba27c21961`. The remote advanced only after
  the source graph was frozen; no upstream bytes were introduced during the
  indivisible build cycle.
- The nine TeX inputs (the driver, seven chapters, and shared notation file)
  contained 471,998 bytes. Their byte-concatenated SHA-256 was
  `ce2b6cca764c3f9267bcc71516edbc1822035d78271f38b220dd56f3d4e80d0e`,
  and the SHA-256 of their ordered checksum list was
  `108ac0c5d69ce91a18e867841b0d4fcf5cab659ae9b556d28db32d826f9a816d`.
  The 189-line, 6,758-byte driver had SHA-256
  `63fb8372dbcb6c0b27eb7dea19e387dea27af23811df9fcfbe9313d37c8180a4`.
- The TeX lane was empty and no generated sidecars were present before the
  build. With `SOURCE_DATE_EPOCH=1788242400`, exactly three uninterrupted,
  strict serial pdfLaTeX passes ran without a source fix or restart. They
  produced 151, 158, and 158 pages. The successive byte counts and SHA-256
  hashes were 2,372,734 and
  `af11e38ba3ecba687b3eea586cbd3305ba440896aa822918aca14ff6e7362e96`;
  2,456,125 and
  `87434d82c9f09a183767bb2a9f0190ef0ae7ae8916a0ea42d1b818b4510b0e34`;
  and 2,456,105 and
  `81d249c8b2bb124836c858bd8e0ef9c8764606a2f9655a798d69e7565b1759b4`.
- The final PDF has 158 A4 pages at 595.276 by 841.89 points. Every page has
  rotation zero; MediaBox, CropBox, BleedBox, TrimBox, and ArtBox are identical
  on all pages; and every page contains extractable text. The document is a
  readable, unencrypted PDF 1.5 with populated title, subject, author, and
  keyword metadata, no JavaScript, and no structural suspect flag.
- All 33 font rows are embedded and subset Type 1 faces; seven are Libertinus
  and none is Type 3. The final log contains no TeX error, undefined reference
  or citation, rerun request, duplicate destination, or overfull box. Its 36
  package warnings (24 hyperref, 11 caption, and one amsmath) and six underfull
  boxes are benign and were included in visual review.
- Poppler rendered all 158 pages. All pages were reviewed in eight complete
  5-by-4 contact sheets. Pages 1, 11, 43, 44, 127, 137, 157, and 158 were also
  inspected at full resolution because they contain the title and proof-status
  legend, the Lagrange crosswalk, dense figures and tables, the PrimePower
  valuation crosswalk, and the final bibliography. No clipping, overlap,
  corrupt image, missing glyph, or unintended blank page was found.
- The canonical validator passes the TeX graph, environment balance, 212
  result environments (149 proof-required), 800 labels, 782 references, 62
  bibliography keys, source disposition, post-pin reconciliation, historical-
  ledger audit, companion-payload provenance, 232-row theorem concordance, and
  canonical source/evidence checks. No package checksum manifest is required.

## Historical canonical publication checkpoints

### Upstream stable-path checkpoint

- Exactly three strict serial pdfLaTeX passes were run after the final path
  edits with `SOURCE_DATE_EPOCH=1788242400`. The first pass refreshed the
  cross-reference state; passes two and three were byte-identical, each writing
  the final 2,934,621-byte artifact with SHA-256
  `00070eafd0734681a7dd125cb64e4c898710c01dc8c8220362550567843bce00`.
- That PDF has 156 pages. Every page is A4 (595.276 by 841.89 points),
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

### Upstream Lagrange-crosswalk checkpoint

- At the later source-only valuation checkpoint,
  `python audit/validate_canonical.py` passed the canonical nine-file TeX
  graph, environment balance, 212 result environments (149 proof-required),
  800 labels, 781 references, 62 bibliography keys, the 180-row source
  disposition, the 23-row post-pin reconciliation, the 151-row historical-
  ledger audit, 111 companion-payload provenance rows for 110 physical
  payloads, the 232-row theorem concordance, and the single exhaustive root
  checksum ledger. The concordance source projection was
  `a065b161c80786829033f1efd39bb5d1e4c521b9b9c4446959a73729a55718e0`.
- The validator's Lean check was intentionally narrow: it confirmed that the
  curated exact and partial-support declaration names occurred in their
  nominated modules. It did not invoke Lean, compare theorem types, or claim
  that the three exact concordance rows were a complete census of formal
  results. Generic decoder synthesis, node biorthogonality, coefficient
  factorization, the full interpolation loop, and the unnormalized decoder
  row-sum law were checked at this identifier level. The geometric Gaussian
  closed-form decoder, its elementary-symmetric/prefactor formula, a typed
  `Matrix` wrapper, and optimization were not claimed. The exact
  `Fabius.twoPowChoose_padicValNat` crosswalk covers only the strict-interior
  dyadic valuation formula. Its module also proves arbitrary-prime forms over
  the positive range through `j = p^m`; the separately stated endpoint-flat
  companion assertion remains unformalized.
- The earlier publication driver had 188 lines, 6,722 bytes, and SHA-256
  `92878edbef877a5e121c96cc80a003bd2137150550c8e05b5cd970ecefe6b248`.
  At the incoming artifact's build checkpoint, the driver, its seven included
  chapters, and the shared notation file had the fixed combined SHA-256
  `941950f6416e8087b209c6c2af596343daca3881c11d44694b1cbc75d3dbe97a`
  throughout the final build cycle.
- After a separate empty-TeX-lane and clean-auxiliary gate, exactly three
  strict, uninterrupted serial pdfLaTeX passes ran from that frozen source.
  All three exited successfully, no other TeX process appeared between passes,
  and no later TeX pass ran. The successive products had 149, 156, and 156
  pages; the final pass wrote 2,452,884 bytes.
- The resulting PDF had 156 pages, 2,452,884 bytes, and SHA-256
  `ea23b4ad19a41c5246b548db7c79e18d50835b697a88e9a5aa2b1188af3b4d35`.
  Every page was 595.276 by 841.89 points (A4), had rotation zero and identical
  MediaBox, CropBox, BleedBox, TrimBox, and ArtBox values, and contained
  extractable text.
- All 33 font rows were embedded and subset Type 1 faces; seven were Libertinus
  and none was Type 3. The document was readable, unencrypted PDF 1.5 with
  populated title, subject, and keyword metadata, no JavaScript, and no PDF
  structural suspect flag.
- The final-pass log contained no TeX error, undefined reference or citation,
  rerun request, duplicate destination, or overfull box. It contained 36
  benign package warnings (24 hyperref, 11 caption, and one amsmath) and six
  underfull boxes; all affected layouts were included in the visual review.
- All 156 pages were rendered and reviewed in six contact sheets. Pages 1, 10,
  37, 38, 45, 149, 150, and 156 were additionally inspected at full size; no
  clipping, overlap, corrupt image, missing glyph, or unintended blank page
  was found.
- The now-retired root checksum manifest exhaustively covered every other
  permanent package file, including the complete evidence tree, without
  duplicate or stale paths, and verified in full at this historical checkpoint. The eight historical source-package
  ledgers summarized by the audit remain unchanged and are not live manifests.

### Replayed-side pre-merge checkpoint

- The publication driver had 189 lines, 6,758 bytes, and SHA-256
  `63fb8372dbcb6c0b27eb7dea19e387dea27af23811df9fcfbe9313d37c8180a4`.
  Those driver bytes remain current after replay, but the complete input graph
  at this checkpoint predates the upstream Lagrange-crosswalk additions.
- Exactly three strict, serial pdfLaTeX passes ran from that source. All three
  exited successfully; no later TeX pass ran.
- The resulting PDF had 157 pages, 2,452,684 bytes, and SHA-256
  `e74c1ee8b12b1ab4df3befcdbbdcef585807eb5f41634e85f32d559bd604866d`.
  Every page was 595.276 by 841.89 points (A4), had rotation zero and identical
  MediaBox, CropBox, BleedBox, TrimBox, and ArtBox values, and contained
  extractable text.
- All 33 PDF font rows were embedded and subset; seven were Libertinus and none
  was Type 3. The document was readable, unencrypted PDF 1.5 with populated
  title, subject, and keyword metadata.
- The final log contained no TeX error, undefined reference or citation, rerun
  request, duplicate destination, or overfull box. It contained 36 benign
  package warnings (24 hyperref, 11 caption, and one amsmath) and six
  underfull boxes; all affected layouts were included in the visual review.
- All 157 pages were rendered and reviewed in four contact sheets. Pages 1,
  79, and 157 were additionally inspected at full size; no clipping, overlap,
  corrupt image, or unintended blank page was found.
- The then-existing checksum records verified against that pre-merge source
  state. They are retained here only as historical receipt facts, do not
  certify the current union, and do not define the current single-root-ledger
  architecture.

### Pre-PrimePower semantic-union build (historical, incomplete gate)

- The 189-line, 6,758-byte publication driver had SHA-256
  `63fb8372dbcb6c0b27eb7dea19e387dea27af23811df9fcfbe9313d37c8180a4`.
  Its source graph combined the general-$q$, endpoint-jet, Lagrange-synthesis,
  reference-appendix, layout, and end-of-appendix edits, but predates the latest
  PrimePower chapter and concordance revision.
- Exactly three clean, strict serial pdfLaTeX passes ran. They produced 151,
  158, and 158 pages; the final two files contained 2,455,521 and 2,455,505
  bytes, respectively. The final PDF has SHA-256
  `2fea6bd2a986dd20aa1301b3d21f4ae3405e3f2a328104baadb85e7c6810f3a0`.
- All 158 pages were A4, rotation zero, and nonblank by extracted text, with
  identical MediaBox, CropBox, BleedBox, TrimBox, and ArtBox values. The file
  was readable, unencrypted PDF 1.5 with populated title, subject, author, and
  keyword metadata, no JavaScript, and no PDF structural suspect flag.
- All 33 font rows were embedded and subset; seven were Libertinus and none was
  Type 3. The final log contained no TeX error, undefined reference or citation,
  rerun request, duplicate destination, or overfull box. It contained 36 benign
  package warnings (24 hyperref, 11 caption, and one amsmath) and six underfull
  boxes.
- The exhaustive page-by-page visual review was not completed, so this build
  never passed the full publication gate even for its own source bytes. The
  later PrimePower source/concordance changes independently make it stale for
  the current tree.

### Local post-PrimePower semantic-union checkpoint

- At this historical checkpoint, the source graph combined the 189-line
  general-$q$/endpoint-jet and
  Lagrange semantic union with the latest 232-row concordance and
  `FabiusFunction.PrimePowerBinomialValuation` crosswalk. The exact dyadic row
  covers only the strict-interior formula; the module's stronger
  arbitrary-prime results include the positive right endpoint, while the
  manuscript's separate endpoint-flat companion remains unformalized.
- From a clean auxiliary state, exactly three strict serial pdfLaTeX passes ran
  without a source fix or restart. They produced 151, 158, and 158 pages. The
  successive PDF byte counts and SHA-256 hashes were 2,372,750 and
  `e41bc034447dcd173a777c91621b8d7b24009c1795eff82f0f05eabbf544b250`;
  2,456,163 and
  `71ff53797c7767f71faade5a1f5b1a9ec4d55bbf6e17284b74687a39dbdde202`;
  and 2,456,153 and
  `2af285713dbb8ebccb01ec839aa9678f06bd4ed8e190483a4eccd827010ecc91`.
- The resulting PDF had 158 A4 pages at 595.276 by 841.89 points. Every page
  had
  rotation zero, identical MediaBox, CropBox, BleedBox, TrimBox, and ArtBox
  values, and nonblank extractable text. It is a readable, unencrypted PDF 1.5
  with populated title, subject, author, and keyword metadata, no JavaScript,
  and no PDF structural suspect flag.
- All 33 font rows were embedded and subset Type 1 faces; seven were Libertinus
  and none was Type 3. The final log contained no TeX error, undefined reference
  or citation, rerun request, duplicate destination, or overfull box. It had 36
  benign package warnings (24 hyperref, 11 caption, and one amsmath) and six
  underfull boxes.
- All 158 pages were rendered and reviewed in eight contact sheets. Pages 1,
  43, 44, 112, 129, 137, and 158 were additionally inspected at full size. No
  clipping, overlap, corrupt image, missing glyph, or unintended blank page was
  found.
- `python audit/validate_canonical.py` passed the nine-file TeX graph,
  environment balance, 212 result environments (149 proof-required), 800
  labels, 782 references, 62 bibliography keys, the 180-row source disposition,
  23-row post-pin reconciliation, 151-row historical-ledger audit, 111
  companion-payload provenance rows for 110 physical payloads, 232-row theorem
  concordance, and the then-current exhaustive root checksum gate. The concordance
  source projection is
  `a065b161c80786829033f1efd39bb5d1e4c521b9b9c4446959a73729a55718e0`.
- The now-retired root checksum manifest exhaustively covered every other
  permanent package file, including that PDF and complete evidence tree,
  without duplicate or stale paths, and verified in full at this historical
  checkpoint. It does not certify the current union.

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
recorded in `../PROVENANCE.md`. The current PDF retains that historical wording
and this record makes its narrower scope explicit. Any future correction to the
TeX provenance sentence is a source edit and therefore requires a new exact
three-pass publication cycle.

## Procedure for a future source edit

After the final TeX edit, use the exact three-pass command sequence in the
canonical README's [build section](../README.md#build-the-canonical-article).
Then inspect the final log for errors, unresolved references, rerun requests,
and overfull boxes; inspect PDF metadata and fonts; render every page; and
visually examine every rendered page. Record the new measurements here, update
the README, refresh `COMPANION_PAYLOADS.csv` if the retained evidence inventory
changed, and rerun the canonical validator without recreating a package
checksum manifest. The current receipt above remains valid only while the
publication-source, documentation, and PDF bytes are unchanged.
