# Author receipt: exact finite language of the 942 Wang tiles

Status: full self-review and fresh bounded compilation PASS. This is an
**author receipt**, not an independent peer review. The new source and checks
are frozen at the hashes below. No existing Lean source, equation, port,
coefficient, or machine data was changed.

## Files and bindings

Paths are relative to `Computability/DiophantineConsistency/`.

| File | Lines | SHA-256 |
|---|---:|---|
| `Lean/DiophantineConsistency/WangTiles942Language.lean` | 298 | `a28056b4929cfea69255619b5d89b5f7a64dc47efe0e94ca2e43e00f7788228d` |
| `Lean/DiophantineConsistency/WangTiles942LanguageChecks.lean` | 71 | `6c41bbf030194613c8f566b4246f94761038ed664e1acea3e68eccaa0744ac4a` |

The main module imports only `DiophantineConsistency.WangTiles942Core`.
Its source bindings were rechecked after compilation:

| Dependency | SHA-256 |
|---|---|
| `WangTiles942Core.lean` | `7471a9ff93f06d0eb39c2f3791d5db28dd2927e6346213173f38c2b3ea150d85` |
| `WangTiles942Data.lean` | `ac9047c705dddbab3bec84265beff2d72d498496bde12261cc76c46dc0c5a125` |
| `DecimalMachine215.lean` | `da9e49c1a5f47a10d1f385810e1e89d2e3f4f25fc438dc85cf2184efdc3c719a` |

The new compiled object is
`.lake/build/lib/lean/DiophantineConsistency/WangTiles942Language.olean`,
SHA-256 `7f9eb9eeaf5581b48c5c7404e92397d4e32f6ac6a5d0c88b8d8c2dc46e101651`.
Existing prerequisite objects were used without rebuilding or overwriting
them. This receipt does not claim a fresh replay of their whole closure.

## Exact finite results

`Allowed` has ten constructors matching every printed family: Start,
transition, plain/halt pass, target-specific receive, finish, the three
initialization cases, reset, and seam. All finite parameters have their
actual ranges. In particular, the receiving family requires membership in
the direction-specific actual target set, and the initialization head tile
is exactly `(3,436,4,4)`.

`row_allowed` and `allowed_row` prove both directions structurally through
the literal lists. `allowed_iff_tile` then transfers through the existing
complete row permutation and length proof:

```lean
Allowed t ↔ ∃ i : Fin 942, WangTiles942.tile i = t
```

This is exact membership, without an added tile or an omitted family. It
does not assert that the family constructors form a disjoint sum. The
transition constructor uses `transitionRow`; the imported
`transitionRow_eq_decoded` proves that row is the actual decimal-decoded
transition. No second unbound action table is introduced.

`action_target_mem` is obtained from the list of all 430 actions and the
proved `targets_eq_cache`. `mem_targets_iff_decoded` proves the converse
as well: a target belongs to a direction set exactly when one of the 430
actual decimal-decoded actions has that direction and target. The halt
target 215 is retained.

Rail bounds and injectivity are finite-set proofs using strict inclusion
of target prefixes:

- Right targets have rails in `6..204`.
- Left targets have rails in `205..249`.
- The two valid directional ranges are disjoint.
- `rail_injective_on` is restricted to the appropriate actual target set.
- `rail_strict_mono` uses membership of its lower argument; it does not
  assert strict increase on arbitrary pairs of unused states.

Induction on `Allowed` proves **both horizontal colors are below 250**.
The transition case uses its own action's direction-specific target
membership, not a bound on an unused opposite-direction rail. Thus every
actual tile has positive horizontal complements `255 - west` and
`255 - east` (in fact both are at least 6).

## Focused checks and limitations

The checks cover the actual halt action 125 and target 215, the terminal
valid rails 204 and 249, first transition `(0,2,7,1)`, the actual initializer
head color 4, a halt receive tile `(204,0,0,432)`, generic restricted
injectivity and directional disjointness, and the uniform complement
bound for every abstract tile index.

A deliberate negative control proves
`rail false 0 = rail false 4`, while `0 ≠ 4`, `0 ∉ targets false`, and
`4 ∈ targets false`. Accordingly, no unrestricted rail-injectivity lemma
is asserted.

There is no tiling, machine-run, occupancy, marked-cycle, halting, or
Con(ZFC) premise in this packet, and no equivalence involving those notions
is claimed. The source is a finite-language foundation for that later
work. All declarations were read in full after implementation and the
final focused checks were reviewed after their elaboration corrections.
No `sorry`, `native_decide`, new axiom, or external archive code was used.

## Fresh compilation

Run from the repository root with Lean `v4.32.0`; both sources explicitly
set `Elab.async false`:

```sh
lake env lean -M6000 -j1 \
  -o .lake/build/lib/lean/DiophantineConsistency/WangTiles942Language.olean \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942Language.lean
lake env lean -M6000 -j1 \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942LanguageChecks.lean
```

Final main compilation: PASS, 4.55 seconds, peak RSS 3,206,564 KB, no
warnings or errors. Final checks: PASS, 10.41 seconds, peak RSS 3,695,128 KB,
no warnings or errors. Timing used `/usr/bin/time`; logs are
`/tmp/wang-language-main.log` and `/tmp/wang-language-checks.log`.

All 12 axiom reports (`action_target_mem`, `decoded_action_target_mem`,
`mem_targets_iff_decoded`, `rail_strict_mono`, `rail_injective_on`,
`right_rail_range`, `left_rail_range`, `directional_rails_disjoint`,
`allowed_row`, `allowed_iff_tile`, `tile_horizontal_bound`, and
`complemented_horizontal_positive`) contain only `propext`,
`Classical.choice`, and `Quot.sound`.

The separately requested audit correction changed the plan's mistaken
`Bridge.ConZFC` name to `DiophantineConsistency.ConZFC`, defined in
`Bridge.lean`. The corrected `reviews/current-wang-machine-language-plan.md`
has SHA-256 `da0155c4a9667cb725d0e9f4902095a3ead77a1c686fec35ca208aa8a26f916f`.
No proof claim was added to that plan.
