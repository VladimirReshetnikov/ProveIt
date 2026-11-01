# Independent equation4-43 display audit

This audit independently matches all 175 Lean, candidate and printed gates,
including 43 variable and four fixed-port input bindings. The exact
sparse-polynomial validator checks 49 definitions and 33 squared residuals;
four mutation controls were rejected. Candidate and full TeX are regenerated
in a temporary directory, and two clean PDF builds match the supplied PDF
byte-for-byte, SHA `8324129e1c251a640b3c04a88bb50e9804a7e3ef5199805443ece579425c613c`.

The separate W-alias check confirms the documented input `WNamed`, computed
gate `WComputed`, and their difference at gate 103. Both pages were visually
inspected: all content is visible, with dense small text on page two. The
retained TeX log has no overfull warnings but reports small font substitutions.
This audits presentation and finite gate computations; native proof provenance
remains a separate historical-provider qualification.
