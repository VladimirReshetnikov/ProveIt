# Independent equation4-44 display audit

This audit independently matches all 176 Lean, candidate and printed gates,
including 44 variable and four fixed-port input bindings. The exact
sparse-polynomial validator checks 50 definitions and 33 squared residuals;
four mutation controls were rejected. Candidate and full TeX are regenerated
in a temporary directory, and two clean PDF builds match the supplied PDF
byte-for-byte, SHA `6e524b5e2a27d36ebe7fdac934013685a08559ea09aac75e06abed8ef1ff9162`.

The separate W-alias check confirms the documented input `WNamed`, computed
gate `WComputed`, and their difference at gate 104. Its first draft searched
for the word "gate" before the input alias and failed closed; that failed
checker and diagnostic are retained. Both pages were visually inspected: all
content is visible, with dense small text on page two. The retained TeX log
has no overfull warnings but reports small font substitutions. This audits
presentation and finite gate computations; native proof provenance remains
a separate historical-provider qualification.
