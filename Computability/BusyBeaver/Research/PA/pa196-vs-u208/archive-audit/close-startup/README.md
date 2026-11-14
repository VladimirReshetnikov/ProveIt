# Common startup for the four closing-decrement candidates

The four archived `pa196_close_cd3.tm` through `pa196_close_cd6.tm` tables
each change one transition of the published dense PA196 machine: row
`(193, 1)` becomes `1 R 17`, `1 R 113`, `1 R 44`, or `1 R 21`, respectively.
`generate.py` checks the pinned archive and member hashes and compares every
row with the corresponding one-row patch. It also checks the hash of the
published table. These archive-byte and parsing checks run in Python; they are
not Lean theorems.

`Common.lean` defines the four patches of the imported
`PA196.Literal.machine`. Its finite table equality theorem checks all 392
numeric simulation rows against the actual Lean literal transition. It proves
that the numeric tape encoding commutes with the imported zipper semantics,
and that a finite numeric trace avoiding both halted controls and the changed
row yields the same exact zipper run for the published machine and every one
of the four patches.

The generator reconstructs a blank-start trace and emits 228 bounded Lean
checks, totaling **58,154 steps**. Each check uses kernel `decide` to verify
the complete intermediate configuration and avoidance condition. The final
`common_startup` theorem composes the checks and shows that the five actual
zipper machines reach one identical configuration in that many steps. Its
numeric representation is
`(75, 1, 152919395647067130113387679226998336721518593)`, where the last two
numbers encode the left and right tape halves with the nearest bit least
significant. State 75 is the dense PA196 root control.

This proves a finite standard-natural-number startup agreement. It does **not**
prove that the four candidates continue to simulate the published source
program, that their complete halting behavior agrees, or any theorem inside
iPRA about PA consistency.

Run with Lean 4.32.0 and the root Lake environment:

```sh
TMPDIR=/dev/shm PA196_CLOSE_JOBS=2 \
  bash Computability/BusyBeaver/Research/PA/pa196-vs-u208/archive-audit/close-startup/check.sh
```

The generated table and trace files are temporary; no large certificate is
committed. Set `PA196_CLOSE_JOBS=1` to check one batch at a time. The script
rebuilds the pinned upstream zipper and literal-machine modules, prints axiom
dependencies for the central theorems, and rejects `sorryAx` in those results.
