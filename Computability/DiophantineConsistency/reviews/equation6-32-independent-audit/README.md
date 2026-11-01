# Independent equation6-32 display audit

This audit independently matches all 142 Lean, candidate and printed gates,
including 32 variable and four fixed-port input bindings. The exact
sparse-polynomial validator checks 41 definitions and 22 squared residuals;
four mutation controls were rejected. Candidate and full TeX are regenerated
in a temporary directory, and two clean PDF builds match the supplied PDF
byte-for-byte, SHA `a28bfd4d6425da01b1ff6289374408b86aa91be5032c4b6436d8decd377316b3`.

The separate W-alias check confirms the documented input `WNamed`, computed
gate `WComputed`, and their difference at gate 102. Both pages were visually
inspected: all content is visible, with dense small text on page two. The
retained TeX log has no overfull warnings but reports small font substitutions.
This audits presentation and finite gate computations; native proof provenance
remains a separate historical-provider qualification.
