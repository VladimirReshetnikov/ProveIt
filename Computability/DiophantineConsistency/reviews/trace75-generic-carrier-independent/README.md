# Independent review: general reverse carrier factor

**PASS.** `Trace75GenericCarrier.positive_carrier` generalizes the existing
`TenPositiveReverseCarrier.positive_carrier` proof from the square factor
`μ*μ` to an arbitrary model-natural D. It assumes precisely `Kpos=H*κ`,
`τ>0`, `y>0` and `κ<f`; the other inputs are model naturals, with no separate
positivity hypothesis on D or f. The proof uses `τ*f*y≥f>κ` to construct
positive n and the exact budget
`n+κ=τ*f*y+u²*(b*t)+t+ρ`. Casting that budget and `Kpos=H*κ` into the
difference ring gives the displayed carrier identity with the offset `D*ρ`.
The same input witnesses are used throughout.

This is generic algebra and does not bind D or the scalar parts to actual
trace75 registers, prove offset divisibility, construct seed data, or establish
halting or an iPRA result.

The accepted `research/trace75-generic-carrier-prototype/observations/carrier-attempt01/`
terminal SHA-256 is `8c74d7c68fad07cd5b1c9ceb8630a5f3655428741f55de362a5cb267bfa6b2e6`;
its regular object `/tmp/trace75-genericcarrier-pj_jvsgp/Trace75GenericCarrier.olean`
has SHA-256 `1b083a3965eadf56fdbe00673ef078ff597f114186e19b3a39bb55a190da84f1`.
Source, copied source, runner, exact axiom report, ten input hashes, first
selected objects for the two direct imports and resource samples were checked.
Tool exit 0 is author-reported; no separate outer receipt or independent Lean
replay is claimed. Full transitive, package, historical and dynamic ancestry
remains outside this review.

`check.py` SHA-256 `fb9f89b9659db2ffb4998e7287a1aab016bc76f3eba924108b8c373ec61ac49e`;
`result.txt` SHA-256 `aaede065e6c3b815e9a380233b747f047af7777afc7d8752287596f29ce94d01`.
