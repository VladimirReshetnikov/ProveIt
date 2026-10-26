# Author receipt: exact north-input grammar

Author: subagent `/root/circuit_reduction`. Status: frozen, full source and
check self-review, fresh bounded Lean module/check compilation PASS. This
is an author receipt, not an independent review.

Paths are relative to `Computability/DiophantineConsistency/`.

| File | Lines | SHA-256 |
|---|---:|---|
| `Lean/DiophantineConsistency/WangTiles942InputLanguage.lean` | 137 | `a28c66e285b3fc652392bc9d58c04135a4fef1f11b4a7e4378a0e02a4416307c` |
| `Lean/DiophantineConsistency/WangTiles942InputLanguageChecks.lean` | 79 | `a5aaa22ade8ea6d6edb6a230006d39149af0a6862dc720656fab763acb11e514` |

The only direct import is the frozen `WangTiles942Boundary.lean`, source
SHA-256 `efda0078ffa174d2d9905cbd3431479a94679479742bbf9ff5856d132b06313c`.
The new object `.lake/build/lib/lean/DiophantineConsistency/WangTiles942InputLanguage.olean`
has SHA-256 `3d31f2f92da50ac436896967d93dad41ed76ca6025de5dfecde8c7bc8d85f4c3`.
No existing source, machine table, frozen packet, or prerequisite object
was changed. No commit was made.

`inputIndex (q : Fin 215) (b : Fin 2)` is exactly the `Fin 430` value
`2*q.val+b.val`; both quotient and remainder are proved to recover `q`
and `b`. `transition_north_eq_index` proves the literal row's north color
is `j.val+2`. This binds the operating-input theorem to the existing
source-action index and the already authenticated `transitionRow`.

All three principal classifications have only `Allowed t` as their tile
hypothesis, and use structural cases rather than enumerating 942 rows:

- `north_operating_iff_transition`: north `headColor q b`, with `q < 215`,
  iff the tile is exactly `transitionRow (inputIndex q b)`.
- `north_halt_iff_pass_or_finish`: north `headColor 215 b = 432+b` iff the
  tile is `(0,432+b,0,432+b)` or `(0,432+b,0,438)`.
- `north_plain_iff`: north `b` iff the tile is plain pass `(0,b,0,b)`,
  plain finish `(0,b,0,438)`, or a receive tile with the same `b` and an
  actual target in its direction-specific target set.

The receive alternative allows halt target 215. Both finish alternatives
remain present; this packet does not eliminate plain finish by a future
whole-row argument. Operating input colors are exactly in 2 through 431,
while the two halt colors are 432 and 433. Source state 215 is not added
to the operating transition domain.

The focused checks bind indices 0 and 429 and the actual halt action
`inputIndex 62 1 = 125`, whose target is 215. They check the first actual
transition tuple `(0,2,7,1)`, the exact input recovery at any table index,
and the rejection of any finish tuple with an operating-head input.
They retain both pass/finish choices at halt inputs and plain inputs,
all target-specific receive choices, and the actual halt receive tuple
`(204,1,0,433)`.

No unique-head, row, strip, computation, run, or halting hypothesis or
semantic equivalence is asserted. The word “operating” is a name for the
finite input-color range here. The transition's authentication to the
literal decimal decoder is inherited from the frozen table packet.

All source and check lines were read before execution. Main passed on
its first build. One check elaboration correction simplified `0 + b`
explicitly; no statement or premise changed. Final commands, from the
repository root with Lean `v4.32.0` and `Elab.async false`:

```sh
lake env lean -M6000 -j1 \
  -o .lake/build/lib/lean/DiophantineConsistency/WangTiles942InputLanguage.olean \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942InputLanguage.lean
lake env lean -M6000 -j1 \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942InputLanguageChecks.lean
```

Main PASS: 4.06 seconds, peak RSS 3,195,660 KB. Checks PASS: 6.62 seconds,
peak RSS 3,674,628 KB. Logs: `/tmp/wang-input-language-main.log` and
`/tmp/wang-input-language-checks.log`; timing from `/usr/bin/time`.
Existing prerequisite objects were reused, not freshly rebuilt.

All nine axiom reports contain only `propext`, `Quot.sound`, and, where
needed, `Classical.choice`. No warnings, `sorry`, new axioms, or
`native_decide`.
