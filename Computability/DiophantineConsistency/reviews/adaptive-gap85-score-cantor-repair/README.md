# Guarded reproduction of the score-coding Cantor dependency

The preliminary 85 score-coding replays directly imported
`BusyBeaver.ZFC.ArithmeticCantor` without guarding that object's resolution.
Their actual selected object is
`/tmp/adaptive13-cell-root-parent-wnvsel13/lib/BusyBeaver/ZFC/ArithmeticCantor.olean`,
SHA-256 `557a0ad1be6af64238890a15739b83875ca2c06ccca047d5ad609afcf45d89b7`.
The original provider's overall state is **FAILED**: it later reached
`ArithmeticWangTable` and exited 137. Its earlier `ArithmeticCantor` and
`Code254` rows both record exit 0. This packet preserves that complete failed
state, the two saved source snapshots and their full logs; it does not
describe the original provider as a passing whole.

`prepare.py` pins the current source, Lean executable, original failed state
and two successful rows, score parent and driver, recorded boundary roots,
and the exact `lean --deps` result. Its manifest records the presence or
absence, hashes and resolved paths of each direct object/companion candidate
across the actual score-provider LEAN_PATH: `Init`, Foundation's
`IOpen.Basic`, `Mathlib.Tactic.Ring`, `Code254` and the selected
`ArithmeticCantor`. There are 500 candidates: 27 present and 473 absent.

Two independently launched `replay.py` processes used the original absolute
source path and historical invocation shape, **without `--root`**, on the
score provider and its recorded boundary. Both exited 0, independently
reproduced the selected object's exact bytes/hash, and matched the old complete
warning log. The original five linter warnings are retained in both full logs;
they were not suppressed. The comparison checks both object and source bytes,
full logs, state fields, source/provider guards and all 500 candidates. A
separate packet audit rechecked both outputs, both old rows and those candidate
guards. `terminal.json` records these actual tool-observed exits after the
fact; it is not an in-process exit wrapper. The two output objects, sources,
logs, states, exact manifest and scripts are preserved here.

This repairs the selected Cantor **direct-input provenance** for a later
guarded score replay; it is not itself a score-coding replay. The selected
Code254 and external direct dependencies are pinned as inputs, but their
transitive project/package source-to-object and dynamic ancestry remains
inherited. The older failed provider's direct import environment was not
traced at its original build time. The new same-source reproductions use the
now-recorded score-provider environment, and matching bytes do not establish
that every historical dependency was independently rebuilt.
