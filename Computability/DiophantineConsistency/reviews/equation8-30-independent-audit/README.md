# Independent equation8-30 candidate display audit

This audits a provisional candidate only. No 30-variable Lean literal exists
here; computed-W positivity, reverse witness construction and native PRA
equivalence remain unproved. The document's disclosure and computed W alias
are checked in `candidate-scope-receipt.json`.

The independent audit checks candidate graph topology/liveness and all 138
candidate/printed gates, including 30 variable and four fixed-port input
bindings. The exact sparse-polynomial validator checks 40 definitions and 21
squared residuals; four mutation controls were rejected. Candidate and full
TeX are regenerated in a temporary directory, and two clean PDF builds match
the supplied PDF byte-for-byte, SHA
`706541982387b38645f81f84a880f042336b459d73d7bb79253f2a9ebbcd1abd`.

Both pages were visually inspected: all content is visible, including the
candidate warning; page two has dense small text. The TeX log reports small
font substitutions but no overfull warning. This is presentation and finite
arithmetic evidence, not a proof of equivalence.
