> FINAL NOVELTY OVERRIDE: B1 is superseded by packet w's shared-edge cyclic architecture. It is comparison evidence only. B2 survives the final late-corpus screen at09d65a93. See `../late_review/`. Historical metrics below describe both exploratory candidates, not credited new savings.

# Round 4: two small closing-row / temporal-composition proof factorizations

Source pin: `e652d21c413de59e4821f6e8e9b6a3a077bf5bfe`.
Source root: `Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.
**Status: complete source-derived Lean candidates, not compiled. No Lean execution,
installation, source-tree mutation, or upstream write was performed.**

## Selection and measured source delta

| ID | Exact source anchor | Preserved contract | Whole source → candidate | Net physical lines |
| --- | --- | --- | --- | --- |
| B1 | `WangTiles942TraceCycle.lean:154–168`, `cycleTile_temporal` | All `H`, `3 ≤ H`, every `k : Fin H` and signed `x`; same wrapped successor and exact north/south equality | 182 → 178 | −4 |
| B2 | `WangTiles942FinishConstruction.lean:29–53`, `passTile_allowed`, `finishTile_allowed` | Every actual `Config 215`, actual `cfg.state = none`, every signed `x`; exact literal pass/finish tuples remain Allowed | 164 → 155 | −9 |

Combined source delta: 346 → 333 physical lines (−13); 290 → 276 nonblank lines
(−14); 15,325 → 14,886 UTF-8 bytes (−439). This is intentionally a small result.
It is not a build-time or proof-term improvement measurement.

B1 adds no helper/API. It rewrites the existing proof only. B2 adds one private
10-line declaration (including its documentation) and two unchanged-public-signature
2-line projection declarations. In the replaced 25-line source span, 16 lines remain;
the new paired helper and its one separating blank line are included in the delta.
No executable definition or public theorem statement changes.

## B1: align the temporal interfaces before classifying rows

The original proof handles `k = 0`, then `k + 1 = H`, then `k + 2 = H`.
Its two final branches are textually identical except for the sign of the same
hypothesis. Those branches already compare the same finish/nonfinish conditional.

The candidate splits first on actual wrap (`k + 1 = H`). On wrap, the successor
is zero, the current row is reset, and `H ≥ 3` excludes `k = 0`. Off wrap,
the successor is `k + 1`, which is nonzero. The two interface expressions have
the same finish condition after associating natural addition. Only the original
initializer output needs the remaining `k = 0` check; its output is the exact
run-time-1 color, and `H ≥ 3` keeps it distinct from finish and reset.

This does not prove temporal matching by assuming a temporal-matching premise.
It consumes the existing, separately derived north/south interface equations
(`TraceCycle:129–151`) and the actual wrapped-index equations (`:74–79`).
It does not change the machine run, add a halting assumption to matching, or
weaken the height guard. The original height-2 negative control is retained.

## B2: derive the halted color once, construct both closing families

Both old Allowed proofs perform the same head/nonhead split and create the
same `Fin 2` tape-bit witness independently. The private `halted_tiles_allowed`
performs those steps once and directly applies the two literal constructors:

```lean
Allowed.pass (a : Fin 2) (b : Fin 2)
Allowed.finish (a : Fin 2) (b : Fin 2)
```

At a halted head `a = 1` and the input color is `432 + b.val`; away from the
head `a = 0` and it is `b.val`. The helper's conclusion is the conjunction of
the two old facts, not an existential package, a new axiom, or a new external
premise. Its tape-bit witness is allocated once and shared across both branches.
The original public statements are projections, retaining the actual halt guard.

Dependencies: `WangMachineEncoding.color` (`:88–90`), `halted_head_color`
(`:62–64`), and the unchanged `Allowed.pass` / `Allowed.finish` constructors
in `WangTiles942Language:128–136`. The finite helper alphabet is exactly
`{0, 1, 432, 433}`. The operating initialized-head color 4 is not silently admitted.

## Novelty relative to the assumed-applied baseline

The baseline auditor inspected research packets `2026-10-26a` through `u`,
the incoming index and the additional latest round-3 six-result delivery.
Both **narrow** obligations were cleared:

* Prior U/round-3 shared-edge step-row work grants spatial edge laws and all
  live-configuration adapters; it does not grant this finite temporal seam
  normalization. B1 claims no credit for those existing spatial interfaces.
* Prior boundary fibers classify existing Allowed tiles; prior reflected halt
  equations concern action state. Neither already derives the two actual
  halted closing constructors from one shared color/head split. B2 claims no
  credit for finite language reflection or generic finite dispatch.

The actual-source metrics above are reproducible from the pinned files. They
are **not** a measured line delta against a materialized fully merged virtual
baseline: that virtual source tree was not created. The residual obligation
assessment is semantic, based on the above specific exclusions. In particular,
no source-window, polynomial-witness packaging, first-exit/prefix selection,
scanner fold, native-rank envelope, translated-interval, equality-reflection,
write-site split, or liveCfg/shared-edge result is counted again.

## Deliberately not selected

* `CurrentCellConstruction2011` binding/reconstruction: the tempting generic
  local-word congruence and local-data packaging directions overlap the
  already-granted source-window/decoder work. No incremental saving claimed.
* `CurrentSoundness2011` and `WangTiles942Completeness`: their public fixed
  polynomial/machine/ConZFC compositions are already short; no conclusion was
  converted into a premise and no new packaging abstraction is proposed.
* `WangTiles942Soundness.marked_halts_before_period`: first-halt/stop-or-live
  reformulations were rejected because first-exit/prefix selection is baseline.
* Four-way `runTile` law bundling: rejected as too close to already-advertised
  liveCfg/shared-edge clients, with no demonstrated incremental benefit.

## Artifacts and validation

* `candidate/`: full edited module candidates.
* `patches/`: independent unified patches against the source pin.
* `build_candidates.py`: exact-source replacement plus measured whole-module deltas.
* `validate_static.py`: comment-aware comparison of existing declaration signatures
  and full definitions, banned-placeholder token scan, symbolic chronology controls.
* `validation/metrics.json`: source/candidate counts and SHA-256 hashes.
* `validation/patch_checks.json`: both `git apply --check` exit codes are 0.
* `validation/static_and_model.json`: 44 existing declarations preserved, no
  changed full definitions, exactly one added private theorem, no placeholder tokens;
  525 symbolic seam checks at heights 3–32, failing-height controls 1 and 2;
  four-color constructor-formula sanity check.

The symbolic model uses opaque labels for initializer input, finish/reset input,
and each actual run time. It validates branch chronology only, not the imported
Lean lemmas or the concrete machine. The four-color model checks the constructor
formula only, not a new enumeration of all 942 tiles. Neither is Lean checking.

### Required later Lean gate (not executed here)

In an authorized checkout at the pin and its recorded toolchain, apply each patch
and elaborate the complete modified file plus its unchanged `Checks` consumer:

```sh
lake env lean DiophantineConsistency/WangTiles942FinishConstruction.lean
lake env lean DiophantineConsistency/WangTiles942FinishConstructionChecks.lean
lake env lean DiophantineConsistency/WangTiles942TraceCycle.lean
lake env lean DiophantineConsistency/WangTiles942TraceCycleChecks.lean
```

Then rebuild the affected downstream closure and inspect the existing
`#print axioms` outputs. The key unverified elaboration points are the concrete
`Fin 2` projection reduction in B2 and the matched conditional normalization
by `Nat.add_assoc` / numeral reduction in B1. Compilation, transitive axioms,
full project build, and performance remain unverified, not failed.
