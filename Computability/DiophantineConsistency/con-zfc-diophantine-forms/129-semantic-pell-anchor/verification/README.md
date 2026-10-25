# Verification receipts

`release_normal_with_rebuild.json` records the successful complete normal-mode
run, including reconstruction of both endpoints and ten byte-exact file
comparisons for each. `release_optimized.json` records the successful
optimization-mode run. These runs preceded final package sealing, so their
`manifest_files_authenticated` field is zero. The shipped `SHA256SUMS` covers
these receipts as well as every other delivery file; the verifier checks that
manifest automatically when it is present.

The four semantic receipts are the separately performed local-identity and
parent-binding checks. `PDF_QA.json` records the final document review.

These files report finite artifact and arithmetic checks. The unbounded
mathematical equivalence is proved in `report.tex` using the stated inherited
interfaces; no complete new kernel proof is claimed.
