# Independent prelaunch review: trace73 gauge sign

**Scoped GO for one guarded author check** using the reviewed source and
runner bytes. This review did not run Lean or exhibit a graph zero.

`research/trace73-gauge-sign/Trace73GaugeSign.lean` has SHA-256
`ec9a9f6a8d14f4913605b72a85fd70142dbfe6c8c077fedb106f6c4620fbb40c`;
`run.py` has SHA-256
`7f5d36ebd8af5c7fbbd77c506150d27708cd28f91442e4fd587b1cf1ade9d520`.

Both proposed lemmas are over a `LinearOrderedCommRing`. The first assumes
the actual h≥1, p₁+v₅≥0 and positive v₁,v₂, and concludes B<0 after the
existing gauge move at t=1; it does not require a graph zero. The second
additionally assumes all coordinates positive, `step p v < v 7`, and an
actual literal trace73 graph zero. It proposes a positive valuation at the
same p with B<0 and the same zero via the gauge identity. The strict center
bound and starting graph zero are explicit premises; no existence of either,
model-natural instantiation, unguarded equivalence or counterexample follows.

All eight selected provider pins match current bytes. Under the planned
search order, gauge, literal, center and pinned trace75/difference-ring
objects resolve first at their pinned paths. The runner checks resources,
rejects errors, warnings and `sorryAx`, and requires an allowed named final
axiom report. It only requires the final report although the source requests
two; a post-run review must inspect both. There is no pinned outer wrapper or
initial source/runner pin in the runner: the orchestrator must reverify the
reviewed bytes before the single launch and retain its actual tool exit.
Full transitive, historical, package and dynamic ancestry remain outside this
review.

## Attempt02 revision: HOLD

The first author attempt failed with missing ordered-ring/tactic imports and
`sorryAx`; it is excluded. Revised source SHA-256
`52f6843ee66cf6e7691d9750c766ea7cd842eb0de2d2b8b52f565b9b00a58fbe`
adds only direct `import Mathlib.Tactic.Linarith`, leaving both statements
unchanged. The unchanged reviewed runner does **not** pin that new direct
import, so do not launch it as attempt02. The current first-selected object is
`/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib/Mathlib/Tactic/Linarith.olean`,
resolved to the Mathlib build, SHA-256
`bbe0c9d1f3d5471ae115ccd10d9ef2f6dc5ec645bad49ee5a04830c178e42091`.
Add an explicit selected-object pin in a new runner and independently review
the revised bytes before launch. All earlier scoped limitations remain.
