# Independent prelaunch review: trace73 gauge

**Scoped GO for one guarded author check** using the reviewed source and runner
bytes. This review did not run Lean, prove positivity, or exhibit a zero.

`research/trace73-gauge/Trace73Gauge.lean` has SHA-256
`0b6060dc6e9917968ca354951efe5ee990866b43eae0ee83ce42d4866394aa72`;
`run.py` has SHA-256
`388718996da8792634ac12cc5c31fe52fda36a2e3ae366170b325c7b4b7ae2e7`.
The all-ring proposed move increases F by h*t, increases alpha by h²*t,
and decreases the center coordinate by s*t, where s=(p₁+w)q+1. Direct
inspection of the literal, centered and trace75 register definitions confirms
the stated rank invariance, `B → B−h*s*t`, center-carrier invariance and
resulting equality of the actual literal evaluator. Positive natural
coordinates, existence of a graph zero and an unguarded equivalence do not
follow from these ring identities.

All seven runner-selected provider pins match current bytes. Under its
recorded planned search order, the literal and center modules and the pinned
trace75/difference-ring objects resolve first at their pinned paths. The
runner samples the process and memory guard, rejects diagnostic errors,
warnings and `sorryAx`, and requires an allowed `graph_move` axiom report.
A separate simulation of its diagnostic regex rejected missing, duplicate and
unexpected-axiom graph reports, `sorryAx` and coded warnings. The runner
requires only the named `graph_move` report although the source requests four
reports; a post-run review must inspect all four. There is no pinned outer
wrapper or initial source/runner pin in the runner itself: the orchestrator
must reverify the reviewed bytes before the single launch and retain its
actual tool exit. Full transitive, historical, package and dynamic ancestry
remain outside this review.

The first author attempt failed because `![...]` was parsed as an invalid
application and produced errors and `sorryAx`; it is not accepted. The revised
source SHA-256 is
`2c505be32fccd400ed3b33fbb68021b882ef69a565da818c3bddac3828a7cf52`.
Its sole change replaces that notation with nested `Function.update` calls at
slots 1, 2 and 7, implementing the same intended move. The runner hash is
unchanged, and all seven pins and current first selections were reverified.
**Scoped GO for one guarded attempt02** on those exact bytes, with the same
outer-exit and four-report post-audit limitations above.

Attempt02 failed with unresolved `Function.update` terms and `sorryAx`; it is
not accepted. The attempt03 source SHA-256 is
`c7a949a6f3622fccc94412f2529603f749a4eb2fd481fdaf31403547e6fc4ece`.
Its only delta changes the `rank_move` and `B_move` proof simplification to
explicit `Function.update_apply`, `norm_num`, and the existing `ring` tactic;
the move, statements and hypotheses are unchanged. The runner and all seven
selected provider bytes and targets were reverified. **Scoped GO for one
guarded attempt03** on those exact bytes, with the same limitations above.

Attempt03 failed in `rank_move` and `B_move` with unresolved update terms and
`sorryAx`; it is not accepted. Attempt04 source SHA-256 is
`ea63e8f4c0c59b5548b972f176bbb33b320cbe71d2968f4603aad6b561ce85c4`.
The sole delta replaces those two proof simplifications with explicit `change`
expressions in `h=p₀*v₀` followed by `ring`; these expressions match the
actual register formulas and intended coordinate updates. Statements,
hypotheses and move remain unchanged. The runner and seven pinned provider
bytes and targets were reverified. **Scoped GO for one guarded attempt04** on
those exact bytes, with the same limitations above.
