# Correction to the bridge's declared read span

This separate correction preserves the original frozen bridge proof and
receipt. It changes only one metadata read span; the mathematical proof,
coefficient recipe, loader and generic compiler claims are unchanged.

The original proof is `positive7_centralizer_projective_bridge_aristotle.md`,
SHA256 `6053c1142c1047deabf59bcd03623d820c268e1e90bf9a6ac8dd8a67bb409c84`.
Its original JSON is SHA256
`7d75570c58566a82fbe447eae2b34d675642443267c67c54b8fe77913f62ed87`.
Both remain byte-for-byte unchanged.

**Correction remark 1 (requested range is not actual read span).** The
original receipt correctly records 159 LF lines for
`positive_matrix_weighted_mass7_aristotle.md`, but incorrectly gives its
actual read span as `[1,210]`. The reading command requested lines 1--210;
the file ends at line 159, so the actual full-file span is **[1,159]**.
The upper command limit was mistakenly copied into the actual-span field.
This is a provenance error, not additional source coverage or a defect in
the weighted-lift mathematics. Root identified it during final receipt review.

The complete 159-line source is bound at commit
`ae670eb58ac7ce9c4816df3cb83e171ce450cba1`, path
`Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/positive_matrix_weighted_mass7_aristotle.md`,
SHA256 `9eb8e934d53fc9954c3413efdb9d8ad38932dcf2df42de6347a8be8da698d977`.
Its current complete bytes were authenticated against that immutable blob.

A fresh byte/read-span metadata check also inspected all nine dependency
declarations and all three peer reread declarations in the original receipt.
This was the only out-of-range span. The accompanying correction receipt
records the corrected spans and verifies every endpoint against the exact
LF line count. No frozen receipt was repaired in place; no scientific code,
word or coefficient evaluation, source replay, build or new checker occurred.

Root read the complete 35-line correction draft and its entire receipt,
including all nine dependency and three peer endpoint checks, and passed
without further correction. This separate pair is now frozen after that
status/provenance update; both original frozen files remain unchanged.
