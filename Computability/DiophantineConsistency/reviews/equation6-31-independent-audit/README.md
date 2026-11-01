# Independent equation6-31 candidate display audit

This audits a provisional candidate only: reverse orientation and native PRA
equivalence are not established. The document's candidate disclosure is
separately checked in `candidate-scope-receipt.json`.

The audit independently matches all 141 Lean, candidate and printed gates,
including 31 variable and four fixed-port input bindings. The exact
sparse-polynomial validator checks 40 definitions and 22 squared residuals;
four mutation controls were rejected. Candidate and full TeX are regenerated
in a temporary directory, and two clean PDF builds match the supplied PDF
byte-for-byte, SHA `837f168fbd08392a09ad94e69e7cdc954d055b8a9f93d57b5d361272fd898e75`.

The separate W-alias check confirms `WNamed`, `WComputed` and their difference
at gate 101. Both pages are visually complete, with dense small text on page
two. The TeX log has no overfull warnings but reports small font substitutions.
This is presentation/finite arithmetic evidence, not a proof of equivalence.
