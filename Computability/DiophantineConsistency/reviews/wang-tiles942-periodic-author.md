# Author receipt: marked cyclic words and periodic plane geometry

Status: frozen; complete source/check self-review and fresh bounded Lean
compilation PASS. This is an author receipt, not an independent review.
The packet proves geometry for the actual 942 tile table. It does not prove
or assume a machine-language calibration theorem.

All paths below are relative to `Computability/DiophantineConsistency/`.

| File | Lines | SHA-256 |
|---|---:|---|
| `Lean/DiophantineConsistency/WangTiles942Periodic.lean` | 128 | `b426e06571ddc25095a0573784d2f289f116cb976468f826da128a4bb9713d53` |
| `Lean/DiophantineConsistency/WangTiles942PeriodicChecks.lean` | 68 | `c8c5ffdd60b4510a573012a3e3688cc1bc80676733c813ec7a0888db6b75e7f6` |

The main imports `DiophantineConsistency.WangTiles942Language` (source
SHA-256 `a28056b4929cfea69255619b5d89b5f7a64dc47efe0e94ca2e43e00f7788228d`)
and `Mathlib.Data.ZMod.Basic`. Its new object
`.lake/build/lib/lean/DiophantineConsistency/WangTiles942Periodic.olean`
has SHA-256 `6f1c769e80e517cfe814714a5a0020f1e9a0ea7f6af976fa72d9f9c49b4f9254`.
No prerequisite source or object was changed or rebuilt for this packet.

`MarkedWord N s a` uses `[NeZero N]`, an arbitrary integer shift `s`, and
an actual indexed tile word `a : ZMod N → Fin 942`. Its complete fields are:

```text
a(0) = 0,
East(a(i)) = West(a(i-1)),
South(a(i)) = North(a(i-cast(s))).
```

In particular there is no unique-Start, rectangle, coprimality,
divisibility, reduced-shift, occupied-cell, run, or halting field. A natural
shift specializes by casting it to an integer. The file does not assert
that any such marked word exists.

The plane is literally

```text
T(x,t) = tile(a(cast(-x-s*t))),   x,t : integers.
```

`address_east` and `address_next_row` prove that increasing `x` subtracts
one from the cyclic address and increasing `t` subtracts `s`. The marked
word conditions consequently give exactly

```text
T(x+1,t).west = T(x,t).east,
T(x,t+1).north = T(x,t).south.
```

`plane_start` gives the actual Start tile `(2,435,3,1)` at `(0,0)`.
`plane_allowed` proves every entry is in the exact finite `Allowed`
language. Both `(N,0)` and `(0,N)` are periods for every shift, and
`marked_periodic_plane` bundles those facts with `0 < N`. No least-period
claim is made. The additional exact helical period `(-s,1)` follows from
the same address identity.

The checks explicitly distinguish subtraction from addition for both
coordinates, exercise negative coordinates and shifts, and instantiate
periodicity at modulus 6 with shift 14 (not reduced, not coprime, and not
a divisor of the modulus). They reconstruct `MarkedWord` from only its
three fields, check the exact Start tuple and both matching orientations,
and specialize arbitrary integer shifts to natural shifts. These are
geometry checks, not examples asserting the existence of a marked tiling.

Both files were read completely before their first compilation; both
passed without development corrections. From the repository root:

```sh
lake env lean -M6000 -j1 \
  -o .lake/build/lib/lean/DiophantineConsistency/WangTiles942Periodic.olean \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942Periodic.lean
lake env lean -M6000 -j1 \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942PeriodicChecks.lean
```

Lean version: `v4.32.0`; both sources set `Elab.async false`. Main PASS in
3.77 seconds with peak RSS 3,199,868 KB. Checks PASS in 3.27 seconds with
peak RSS 3,174,860 KB. Logs: `/tmp/wang-periodic-main.log` and
`/tmp/wang-periodic-checks.log`; timing is from `/usr/bin/time`.

All eleven axiom reports use only `propext`, `Quot.sound`, and, where
needed, `Classical.choice`. There are no warnings, `sorry`, new axioms, or
`native_decide`. No frozen mathematical packet, maintained page, or shared
source was edited; no commit was made.
