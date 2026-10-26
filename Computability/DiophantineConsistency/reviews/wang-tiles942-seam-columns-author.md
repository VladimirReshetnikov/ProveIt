# Author receipt: seam columns in integer time

Author: subagent `/root/circuit_reduction`. Status: frozen, full source and
check self-review complete, fresh bounded Lean compilation PASS. This is
an author receipt, not an independent review.

Paths are relative to `Computability/DiophantineConsistency/`.

| File | Lines | SHA-256 |
|---|---:|---|
| `Lean/DiophantineConsistency/WangTiles942SeamColumns.lean` | 106 | `654d4b1c570526742157496f96b312fc8dd32a32a7a0b629840f6f6486dbc6c4` |
| `Lean/DiophantineConsistency/WangTiles942SeamColumnsChecks.lean` | 87 | `8101f6b08db7a71a2e19d29ed71b08b3d13b27131dfdcc7f1dce77bda3ae7ef8` |

Direct imports are the frozen `WangTiles942Boundary.lean` (SHA-256
`efda0078ffa174d2d9905cbd3431479a94679479742bbf9ff5856d132b06313c`)
and `WangTiles942Periodic.lean` (SHA-256
`b426e06571ddc25095a0573784d2f289f116cb976468f826da128a4bb9713d53`).
The new object `.lake/build/lib/lean/DiophantineConsistency/WangTiles942SeamColumns.olean`
has SHA-256 `f37ba20f3f91286bef6d89e732f73e7068014f4949d82e63f64a59a88ebef2df`.
No prerequisite source or object was changed or rebuilt.

## Generic theorem scope

For `T : ℤ → ℤ → Tile`, `SeamAt T x t` means `(T x t).north = 437`.
The generic temporal results have exactly these two premises:

```text
∀ x t, Allowed (T x t),
∀ x t, (T x (t+1)).north = (T x t).south.
```

Local boundary classification first gives north 437 iff south 437.
Combining that with time matching proves `SeamAt T x (t+1)` iff
`SeamAt T x t`. Integer induction, including the negative-time step,
proves `seam_iff_zero`; `seam_iff_time` compares any two integer times.
There is no horizontal matching or periodicity hypothesis in these
results. The proof premises are explicitly included in the generic
section, which ends before the marked specialization.

`column_seam_tuples` proves that a seam at any single time forces every
tile in that column, at every integer time, to be one of the actual nine
seam tuples `(a²,437,b,437)` with `a,b : Fin 3`. Its existential-time
variant has the same conclusion. The finite parameters may vary with
time; the result does not say the entire tile is time-constant.

`start_column_not_seam` and `start_column_vertical_ne` prove that a Start
at any one time rules out both seam-color edges throughout that column.
They do not assert that every tile in that column is Start.

The marked-word specialization uses the exact existing pullback plane,
its proved allowedness, its actual time matching, and its Start at the
origin. In particular `marked_origin_never_seam` rules out both north and
south color 437 at `(0,t)` for every integer `t`. No additional alignment,
uniqueness, run, strip, or halting premise is added.

## Focused premise checks

The checks include:

- A constant allowed seam family that satisfies time matching but fails
  horizontal matching. The generic theorem still applies, including from
  time -31 to time 17.
- An everywhere-allowed family whose seam exists only at time zero. The
  checks prove time matching fails, so allowedness alone is insufficient.
- A time-matching family whose seam exists only at time zero but whose
  zero-time tile is not allowed. Thus time matching alone is insufficient.
- A Start at an arbitrary non-origin coordinate/time `(7,-5)`, with both
  seam colors excluded at every time, and the exact marked-origin wrapper.

These are geometry and premise-binding checks. They make no assertion
that an actual marked word exists, and no machine semantics is claimed.
The optional horizontal color classification was assigned to another
agent and is absent from this packet.

## Fresh compilation and audits

Both source files were read in full before their final builds. Development
corrections explicitly included the generic proof premises and replaced
two finite-constructor simplifications with direct exact terms; no
mathematical assumption was weakened. From the repository root:

```sh
lake env lean -M6000 -j1 \
  -o .lake/build/lib/lean/DiophantineConsistency/WangTiles942SeamColumns.olean \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942SeamColumns.lean
lake env lean -M6000 -j1 \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942SeamColumnsChecks.lean
```

Lean `v4.32.0`, `Elab.async false`: final main PASS in 3.29 seconds,
peak RSS 3,197,352 KB; final checks PASS in 3.24 seconds, peak RSS
3,183,768 KB. Logs are `/tmp/wang-seam-columns-main.log` and
`/tmp/wang-seam-columns-checks.log`; timing used `/usr/bin/time`.
Existing dependencies were reused, not freshly rebuilt.

All eleven printed axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. No warnings, `sorry`, new axioms,
`native_decide`, edits to frozen/shared mathematical sources, or commits.
