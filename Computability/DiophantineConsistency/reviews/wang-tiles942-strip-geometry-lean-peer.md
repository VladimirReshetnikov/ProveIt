# Independent review of the actual 942-tile strip geometry

Verdict: **PASS**, 2026-10-26. Reviewer: the circuit-reduction agent; author of the reviewed composition: root. I read the complete 90-line module and 42-line checks, read the complete 148-line `WangTiles942InitialStrip.lean` and its author receipt, and checked the imported finite horizontal and seam interfaces. No source changes were requested or made.

## Frozen source binding

All paths below the repository's `Computability/DiophantineConsistency/` directory:

| File | SHA-256 |
| --- | --- |
| `Lean/DiophantineConsistency/WangTiles942StripGeometry.lean` | `2439e3e5bd3b9f4eeea38013e4a2e237444626cc5864b0244463be8a88ce4e7a` |
| `Lean/DiophantineConsistency/WangTiles942StripGeometryChecks.lean` | `2c68d346ff2075c41fab3e96b1e106bd4034ac33300a5b779419a59aac7a8aaf` |
| `Lean/DiophantineConsistency/WangTiles942InitialStrip.lean` | `b20872f398fc330069ba8eec137d295bc6f6418b6c215a53afcff6334128a100` |
| `Lean/DiophantineConsistency/WangTiles942InitialHorizontal.lean` | `f989a80b56aac3c1ee31f41fc18cd4e4ac0486bbce73cb22d220f6630ced9536` |
| `Lean/DiophantineConsistency/WangTiles942SeamColumns.lean` | `654d4b1c570526742157496f96b312fc8dd32a32a7a0b629840f6f6486dbc6c4` |
| `Lean/DiophantineConsistency/WangTiles942Periodic.lean` | `b426e06571ddc25095a0573784d2f289f116cb976468f826da128a4bb9713d53` |

The controller-certificate agent authored InitialStrip and InitialHorizontal. I authored Periodic and SeamColumns. This receipt is an independent review of root's new composition and its use of those interfaces, not a claim that I independently authored or independently audited my own dependencies.

## Mathematical review

`initial_tile` covers **every integer position** strictly between the walls. For negative positions it converts `-x` to a natural number and proves the needed cast and range facts before invoking `left_inside`; nonnegative positions split into 0, 1, and the right interior. The strict inequalities correctly include the two distinguished positions even when either extra blank tail is empty. The four resulting tuples have nonseam north and south colors. `initial_south` gives exactly 1 at position 0, 4 at position 1, and 0 elsewhere inside the strip. This is a statement about the actual tile colors, not an additional formal machine-step theorem.

`persistent_of_initial` uses only an exact InitialStrip, Allowed at every plane location, and the temporal matching equation. Both walls have north 437 at time 0, and the seam-column theorem supplies an actual one-of-nine seam tuple at every integer time. Every interior location is nonseam at time 0 and stays nonseam by the same equivalence. The south-color exclusion follows from the exact Allowed north/south 437 equivalence. Seam parameters may vary with time; the theorem does not silently assert a fixed seam tuple.

The generic composition does not need an extra horizontal assumption because its InitialStrip input already contains the horizontal conclusions. The final `marked_persistent_strip` wrapper supplies that input from `MarkedWord` using the actual plane, horizontal matching, period, and marked origin. Its only external premise is `MarkedWord N s a` with `NeZero N`: there is no unique-Start, width/height divisibility, coprimality, rectangle, machine-run, or halting hypothesis. The integer wall positions are distinct, but the theorem does not assert that their residue classes modulo N are distinct.

The checks retain all wall bounds, both distinguished interior positions, seed colors 1 and 4, and nonseam status at arbitrary integer times. The five reported theorems contain no hidden stronger premise than the source signatures.

## Fresh isolated replay

I constructed `/tmp/wang942-strip-geometry-circuit-peer/DiophantineConsistency/` with symlinks to the existing dependency object entries, excluding the reviewed module's own entries. I then compiled a new object there and put this overlay first on `LEAN_PATH` for the checks. No prerequisite or shared object was overwritten. This reuses available prerequisite objects; it is not a fresh replay of their full closure.

```sh
lake env lean -M6000 -j1 \
  -o /tmp/wang942-strip-geometry-circuit-peer/DiophantineConsistency/WangTiles942StripGeometry.olean \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942StripGeometry.lean
lake env bash -c 'export LEAN_PATH="/tmp/wang942-strip-geometry-circuit-peer:$LEAN_PATH"; exec lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942StripGeometryChecks.lean'
```

Both commands exited 0. Main: 3.90 seconds, peak 3,198,216 KiB. Checks: 3.17 seconds, peak 3,176,896 KiB. The main emitted no Lean diagnostics. The checks emitted only the intended five axiom reports. `initial_tile` and `initial_vertical_nonseam` use `propext` and `Quot.sound`; the other three audited theorems additionally use `Classical.choice`. No `sorryAx`, new axiom, or native-decision axiom appears.

| Replay artifact | SHA-256 |
| --- | --- |
| Isolated `WangTiles942StripGeometry.olean` | `4a361434b60455f0e750a60a7de1f7e0fa1ed381b3e41cbba30283baa4efb934` |
| `/tmp/wang942-strip-geometry-circuit-peer/main.log` | `aaf927b9e5c5597f37ebaac4ce17e17fa08f18b10cb0641f85bc2d8c0da19548` |
| `/tmp/wang942-strip-geometry-circuit-peer/checks.log` | `341d388a78c2bfe7afafc72ba2e3dbe134f95bfdd5dd63da7c58b4bd119c8167` |

The source hashes were rechecked after replay. This packet proves persistent geometric walls and a seeded finite initial interval. It does not establish actual row-by-row machine dynamics, eventual halt, a tiling/run equivalence, or a consistency endpoint.
