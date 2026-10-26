# Cyclic tile-word construction: author receipt

Date: 2026-10-26. Author: `controller_certificate`. This is an author
self-review. The two new Lean sources below are frozen; both final
bounded builds passed. No independent review is asserted here.

## Exact files and dependencies

Source paths are relative to
`Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

| File | Lines | Bytes | SHA-256 |
| --- | ---: | ---: | --- |
| `CurrentWordConstruction2011.lean` | 186 | 8698 | `9455d6c2015906a8f76ff2be5275a95cae5340f0ca3e8dc16666ffc6bab2b5b8` |
| `CurrentWordConstruction2011Checks.lean` | 85 | 3823 | `79ac21538dc3f6724a26e3a7e7e57b6643a4d5470977e19f0c881d66f0b6dd12` |

The main imports exactly these frozen modules:

| Import | SHA-256 |
| --- | --- |
| `CurrentCellConstruction2011` | `03344f81c7817f625633470218727176f975ee7617154589534a0b94feb9bd0a` |
| `CurrentCellCoordinate2011` | `6e316a7a9a0107e8bc2bc41bf2bcd5868251b297f0b5cd7c79b64a52da1e9f48` |
| `WangTiles942Periodic` | `b426e06571ddc25095a0573784d2f289f116cb976468f826da128a4bb9713d53` |

I authored the local construction and earlier label/translation
dependencies. `complemented47_review` authored the coordinate and cell
cycle modules; `circuit_reduction` authored the periodic-language module.
I read the complete coordinate/cycle/translation APIs and the relevant
local-construction and periodic definitions before implementing this
composition. The cell-cycle source remains
`874a68dc11255170f19dc1a5345e195f36379711f8af630b16dd6eb9fe77081d`.
No dependency was edited.

## Definition and proved scope

For `a : ZMod N → Fin 942`, independently supplied natural-valued maps
`dummy` and `marker`, and `k : ZMod (N*2011)`, the definition uses

```text
j = (k.val / 2011 : ZMod N),  e = k.val % 2011,
word a dummy marker k =
  if e = 977 then dummy j
  else if e = 1004 then marker j
  else localDigit (a j) e.
```

`word_boolean` requires only that the two supplied control maps are
Boolean. `word_support` proves zero outside the literal fixed low-mask
support, without a Boolean premise. In particular the physical marker
slot is retained even though its reflected coefficient is zero.

The canonical base `base j` is the cast of `j.val*2011` into the full
cyclic group. `base_add_val`, `base_add_field`, and `base_add_index`
prove the exact representative, field and tile index for every
`e<2011`. The representative bound is proved using `j.val<N`; there is
no truncation assumption about the last cell. `base_natCast` and
`word_at_nat_base` also handle arbitrary natural base indices, including
indices several full periods beyond `N`, by the existing scaled-cast
identity. Neither coprimality nor `N>1` is assumed.

`word_at_base` gives the exact three-way slot formula. `word_data`
recovers local data at every `e<986` other than dummy977, and
`word_dummy`/`word_marker` give the two independent control maps exactly.
The compatibility lemmas from the local-cell packet then prove:

- `word_selected`: the unique selected abstract tile is `a j` through
  the actual physical permutation;
- `word_copiedWord`: the full packed complemented label word is
  `complementedTile (a j)`;
- `word_selectorPayload`: the exact selector payload is
  `1 + packedTile (tile (a j))`;
- `word_selectorCount`: the existing physical selector count is one.

`base_eq_coordinate` and `base_coordinate` identify this construction
with the established `Cell N` equivalence exactly. `word_at_cell` and
`word_cell_data` expose the same slot, selector and label identities at
an arbitrary aligned cell, with no replacement of the digit function.

`word_origin` is one exactly when `a 0 = 0`; `word_origin_of_marked`
discharges that condition using only `MarkedWord.start_at_zero`. It
does not assume that Start occurs nowhere else.

The optional definition `shiftedStartMarker a stride j` is the Boolean
indicator of `a (j+stride)=0`. Its Boolean property and exact equality
criterion are proved. The addition sign is explicit, but this packet
does not assert that the chosen map already satisfies a temporal-copy
constraint. That constraint still needs its own orientation proof.

This packet constructs the global Boolean sparse word and its local
data, not the full reverse native arithmetic witness. It does not prove
all copy tests, high-mask tests, carry normalization, controller
congruences, rank constraints, or positive polynomial existence. No
native calibration, desired equivalence, tiling matching, high-mask or
carry premise is hidden in the assembly results.

## Fresh builds and checks

I read all new source before execution and reread both complete final
files after the last correction. Builds were sequential using the
pinned Lean 4.32.0 toolchain, `Elab.async false`, and the capped commands:

```sh
lake env lean -M6000 -j1 \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentWordConstruction2011.lean \
  -o .lake/build/lib/lean/DiophantineConsistency/CurrentWordConstruction2011.olean
lake env lean -M6000 -j1 \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentWordConstruction2011Checks.lean \
  -o .lake/build/lib/lean/DiophantineConsistency/CurrentWordConstruction2011Checks.olean
```

The final main build exited zero in 4.77 seconds, peak 3271132 KiB,
with no Lean diagnostics. The final checks exited zero in 4.35 seconds,
peak 3255280 KiB. All 22 printed axiom reports contain only the standard
axioms `propext`, `Classical.choice`, and/or `Quot.sound`. No `sorry`,
`admit`, new axiom, or `native_decide` occurs.

Focused examples cover the final cell's last field and exact wrap,
an entire-modulus offset, seventeen whole periods at `N=1`, the full
copied-word identity at `N=1`, Boolean/support properties with separate
control maps, the aligned-cell adapter, origin Start and non-Start,
and the optional marker's explicit addition sign.

The first main attempt needed explicit simplification of local `let`
bindings and numeral casts, plus an explicit unfolding of the selector
count to its weighted-sum form. Its final build passed cleanly. The
first checks attempt needed only `Nat.cast_ofNat` in the `N=1`
seventeen-period example; the corrected final checks passed. These
were elaboration corrections, not weakened mathematical statements.

| Output | SHA-256 |
| --- | --- |
| Main `.olean` | `f8541db6af0c613bc9f05c5934d35b9edbadd1887220725644cd8d9ac44a3199` |
| Checks `.olean` | `96fdd67ea6959fb509e91e5fbd5dcb9cd5e166c25587ba1d4b3273935ed2cba2` |
| `/tmp/current-word-construction2011-main-stage1.log` | `b95cdf562d31551ea09adae63c3847b5352b6a6fff73a1bcb7498058a7eb8fec` |
| `/tmp/current-word-construction2011-main-stage2.log` | `8d96f1cf85152ebe371b4010fff5ceffa33cff7b612e5c6d52bdc7cb690575f6` |
| `/tmp/current-word-construction2011-checks-stage1.log` | `c922cb4fcd3892a841a87cffae781634957ef6d5bc537b862f7d026c4ea9ac1c` |
| `/tmp/current-word-construction2011-checks-stage2.log` | `89867177714085839e6cd28a29826703df3eeef751a5d3314b6517e0b27a1d72` |

Only the assigned new module, checks and this receipt were added. No
frozen source or shared status document was changed, and no git operation
was run.
