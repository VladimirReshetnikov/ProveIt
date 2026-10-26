# Author receipt: finite initialization strip around Start

Date: 2026-10-26 UTC. Author: `controller_certificate`, at root's assignment.
Status: frozen; full new source/check self-read and fresh bounded Lean
compilation PASS. This is an author receipt, not an independent review.
Only new files were authored; frozen modules and maintained equations were
not modified.

All source paths are relative to `Lean/DiophantineConsistency/`.

| File | Lines | SHA256 |
| --- | --- | --- |
| `WangTiles942InitialStrip.lean` | 148 | `b20872f398fc330069ba8eec137d295bc6f6418b6c215a53afcff6334128a100` |
| `WangTiles942InitialStripChecks.lean` | 66 | `76f7e6be2f41bac54a1399dd40c4ee6875fedf34eb10da111ebce72168c1c442` |
| Imported `WangTiles942InitialHorizontal.lean` | 136 | `f989a80b56aac3c1ee31f41fc18cd4e4ac0486bbce73cb22d220f6630ced9536` |
| Imported `WangTiles942Periodic.lean` | 128 | `b426e06571ddc25095a0573784d2f289f116cb976468f826da128a4bb9713d53` |

The author also authored InitialHorizontal. Circuit authored Periodic.
Both complete dependency sources had been read before this implementation,
and their relevant exact color and signed-row identities were rechecked.
Both complete new files were read before execution.

`periodic_initial_strip` takes an arbitrary row `T : ℤ → Tile`, local
membership `Allowed(T x)` at every integer position, actual horizontal
matching `West(T(x+1))=East(T x)`, a positive natural period `N`, and
`T 0=Start`. It assumes no seam, finite strip, unique Start, time matching,
machine run or rectangular geometry.

The exact `InitialStrip T N L R` conclusion records:

- `0<L≤N` and `2≤R≤N+1`;
- Start at0 and the actual head initializer `(3,436,4,4)` at1;
- a left wall `T(-L)=(a²,437,2,437)` for some `a : Fin 3`;
- a right wall `T(R)=(4,437,b,437)` for some `b : Fin 3`;
- `T(-j)=(2,434,2,0)` for every `1≤j<L`;
- `T(j)=(4,436,4,0)` for every `2≤j<R`.

Tuple order is West/North/East/South. The separate `wall_north` projection
gives north color437 at both walls, while retaining the stronger exact
tuple witnesses in the structure.

The head is forced immediately: Start's east color3 matches its right
neighbor's west color3, whose exact local classification is initHead.

On the left, periodicity gives `T(-N)=Start`, a non-initLeft witness at
positive distance at mostN. `Nat.find` chooses the least positive distance
`L` whose tile is not initLeft. Every smaller positive distance is therefore
initLeft. The tile immediately to the right of `-L` is Start if `L=1` and
initLeft otherwise, so its west color is2 in either case. Matching makes
the candidate wall's east color2. The exact classification gives initLeft
or a seam with east2; minimality's failure condition excludes initLeft.

On the right, periodicity gives `T(N+1)=T1=initHead`, a non-initRight
witness at distance at least2. The least failure distance `R` similarly
bounds all intermediate positions. Its immediate predecessor is initHead
when `R=2`, and initRight otherwise; both have east color4. Matching forces
west4 at the candidate wall, and its non-initRight condition leaves exactly
the seam alternative. All conversions between natural predecessor distances
and integer coordinates are proved under the relevant positive bounds.

These are two finite first-failure arguments, not assumed boundary
conditions. No claim that the two wall coordinates have distinct residues
moduloN is made. Their distinct integer positions enclose the displayed
finite initialization segment. Repeated Start tiles elsewhere in the row
are allowed by the hypotheses.

`marked_initial_strip` applies the theorem to row0 of the exact signed
plane pullback of any `MarkedWord N s a`. It derives all tile memberships,
horizontal matching, periodN and origin Start from that existing structure.
The shift is arbitrary and need not be coprime toN; no machine semantics is
introduced by this specialization.

Focused checks expose the requested numerical wall bounds and all interval
tiles, verify the bottom colors0 on both initializer tails, Start's south1
and the actual head's south4, and retain both walls' facing colors and south
seam color437. The marked-word specialization is checked without an
additional strip premise.

Fresh sequential commands, with Lean `v4.32.0`:

```sh
lake env lean -M6000 -j1 -o .lake/build/lib/lean/DiophantineConsistency/WangTiles942InitialStrip.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942InitialStrip.lean
lake env lean -M6000 -j1 -o .lake/build/lib/lean/DiophantineConsistency/WangTiles942InitialStripChecks.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942InitialStripChecks.lean
```

Both files passed their first execution. Main diagnostics are empty,
SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
The checks log SHA256 is
`1f222f1bde6b6959a748b90d6f7b6cff2bac9ffc13d599977a8f1b65a2ed5002`.
All six printed theorem axiom sets use only `propext`, `Classical.choice`
and `Quot.sound` (the wall projection requires only `propext`). No custom
or native-evaluation axiom occurs. Existing prerequisite objects were
reused; this is not a fresh-closure compilation claim.

Scope: the packet proves a bounded initial horizontal segment and exact
seam walls. Seam-column time invariance, a later reset/finish row, machine
step decoding, the reverse arithmetic construction and the consistency
equivalence remain separate obligations.
