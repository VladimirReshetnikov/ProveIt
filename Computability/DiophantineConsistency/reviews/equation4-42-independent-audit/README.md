# Independent equation4-42 candidate display audit

This audits a provisional candidate only: reverse orientation and native PRA
equivalence are not established. The document's candidate disclosure is
separately checked in `candidate-scope-receipt.json`.

The audit independently matches all 174 Lean, candidate and printed gates,
including 42 variable and four fixed-port input bindings. The exact
sparse-polynomial validator checks 48 definitions and 33 squared residuals;
four mutation controls were rejected. Candidate and full TeX are regenerated
in a temporary directory, and two clean PDF builds match the supplied PDF
byte-for-byte, SHA `b9a6b76ef4e397e23b1262c502fee573c25ac4dd8affaadf4034aea1071e1715`.

The separate W-alias check confirms `WNamed`, `WComputed` and their difference
at gate 102. Both pages are visually complete, with dense small text on page
two. The TeX log has no overfull warnings but reports small font substitutions.
This is presentation/finite arithmetic evidence, not a proof of equivalence.
