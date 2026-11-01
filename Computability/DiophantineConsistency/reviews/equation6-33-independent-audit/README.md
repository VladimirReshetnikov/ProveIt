# Independent equation6-33 display audit

This audit independently matches all 143 Lean, candidate and printed gates,
including 33 variable and four fixed-port input bindings. The exact
sparse-polynomial validator checks 42 definitions and 22 squared residuals;
four mutation controls were rejected. Candidate and full TeX are regenerated
in a temporary directory, and two clean PDF builds match the supplied PDF
byte-for-byte, SHA `1b5ccdd439ed539f7894909fc8e8aba27af2596317de500bc5577dbd20a62b21`.

The separate W-alias check confirms the documented input `WNamed`, computed
gate `WComputed`, and their difference at gate 103. Both pages were visually
inspected: all content is visible, with dense small text on page two. The
retained TeX log has no overfull warnings but reports small font substitutions.
This audits presentation and finite gate computations; native proof provenance
remains a separate historical-provider qualification.
