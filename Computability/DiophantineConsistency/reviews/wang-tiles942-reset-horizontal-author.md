# Author receipt: horizontal color 1 and exact reset cases

Author: subagent `/root/circuit_reduction`. Status: frozen, complete source
and check self-review, fresh bounded Lean compilation PASS. This is an
author receipt, not an independent peer review.

Paths are relative to `Computability/DiophantineConsistency/`.

| File | Lines | SHA-256 |
|---|---:|---|
| `Lean/DiophantineConsistency/WangTiles942ResetHorizontal.lean` | 92 | `1cba7e914d13a2d6053b5d35b7b308f08093ae99d36c8963952f0de05f663ebc` |
| `Lean/DiophantineConsistency/WangTiles942ResetHorizontalChecks.lean` | 69 | `c15cc9f8fd6844b4d0f8f8169f2ba0912709a5bc91522aae219614d6c1651254` |

The sole import is `DiophantineConsistency.WangTiles942Language`, source
SHA-256 `a28056b4929cfea69255619b5d89b5f7a64dc47efe0e94ca2e43e00f7788228d`.
The new object `.lake/build/lib/lean/DiophantineConsistency/WangTiles942ResetHorizontal.olean`
has SHA-256 `1be23fb4369ddd49e404eb4a0a0f5fa891086777436c3618511e8fbbcfbf54fc`.
No prerequisite source/object, frozen packet, or shared source was changed.
No commit was made.

`horizontal_one_cases` exhausts the exact `Allowed` families. For
transitions it uses membership of the action's own target in its actual
direction set; for receive tiles it uses the constructor's target
membership. The proved valid-rail lower bound 6 excludes color 1, while
inactive edges are exactly zero. No unrestricted rail or target premise
is substituted.

The resulting exact local equivalences are:

```text
west = 1 iff reset(1,438,1,p), p in [434,435,436],
             or seam(1,437,b,437), b : Fin 3;
east = 1 iff the same reset family,
             or seam(a²,437,1,437), a : Fin 3.
```

`west_1_nonseam`, `east_1_nonseam`, and `horizontal_one_nonseam` explicitly
require `north ≠ 437` and return the complete reset tuple with its exact
three-element south-color membership. The final local corollary
`north_438_of_horizontal_one_nonseam` extracts north color 438 for later
color matching.

The checks preserve every seam alternative, including east-1 seams with
west colors 0 and 4. They prove that the allowed seam `(1,437,1,437)` has
both horizontal edges 1 but is not a reset, so the nonseam hypothesis is
necessary. They also reject a forged reset with south color 433, check
all three allowed reset parameters, and instantiate the conclusions at
an arbitrary actual table index.

No row, adjacency, run, strip, halting, or all-reset-row premise or result
is included. In particular, this packet does not claim that a local
finish constructor has machine-halting semantics.

Both files were read fully before execution and passed on their first
fresh compilation. From the repository root, Lean `v4.32.0`, with
`Elab.async false`:

```sh
lake env lean -M6000 -j1 \
  -o .lake/build/lib/lean/DiophantineConsistency/WangTiles942ResetHorizontal.olean \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942ResetHorizontal.lean
lake env lean -M6000 -j1 \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942ResetHorizontalChecks.lean
```

Main PASS: 3.34 seconds, peak RSS 3,198,940 KB. Checks PASS: 3.15 seconds,
peak RSS 3,176,312 KB. Logs: `/tmp/wang-reset-horizontal-main.log` and
`/tmp/wang-reset-horizontal-checks.log`. Timing used `/usr/bin/time`.
Prerequisites were reused, not freshly rebuilt.

All seven axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. No warnings, `sorry`, new axioms, or `native_decide`.
