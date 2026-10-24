# Verification records

`REPLAY_NORMAL.json` and `REPLAY_OPTIMIZED.json` are successful runs of the root verifier on temporary copies of the delivered components. They include the independent exact cleared-norm checker. Component receipts give further details.

These replay receipts were captured before the final content manifest was created, so their `manifest_files_checked` field is zero. After all proof, provenance, and PDF files were assembled, every manifest hash and every ZIP member was checked separately. Running the delivered root verifier now checks that manifest before replaying the mathematics-related finite checks.

`PDF_QA.json` records compilation and visual inspection of the final 20-page article. The integer and direct independent reviews are within their respective components. The report states the distinction between finite algebra/data checks, new ordinary mathematical proofs, and inherited unbounded calibration.
