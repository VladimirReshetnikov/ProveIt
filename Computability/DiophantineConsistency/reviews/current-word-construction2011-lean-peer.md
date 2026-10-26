# Cyclic tile-word construction: independent Lean review

Date: 2026-10-26. Reviewer: `circuit_reduction`. Author: `controller_certificate`.
Verdict: PASS, with no requested source changes. This is an independent review of
word assembly and its stated local interfaces, not a proof of the complete
reverse arithmetic construction.

## Frozen sources and review scope

Paths below are relative to `Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

| File | Lines | SHA-256 |
| --- | ---: | --- |
| `CurrentWordConstruction2011.lean` | 186 | `9455d6c2015906a8f76ff2be5275a95cae5340f0ca3e8dc16666ffc6bab2b5b8` |
| `CurrentWordConstruction2011Checks.lean` | 85 | `79ac21538dc3f6724a26e3a7e7e57b6643a4d5470977e19f0c881d66f0b6dd12` |

I read both entire sources and the entire author receipt
`reviews/current-word-construction2011-author.md`
(SHA-256 `88e6050ad1982182f94ba7ca9513ef75a5ebf024a1dc0198c15e9778890131e3`)
before execution. I read the complete cell-coordinate and cell-cycle modules,
and had independently reviewed the complete local-cell construction and checks
immediately before this task. I checked the actual imported definitions rather
than assuming a new tile permutation or a renamed East/West field layout.

| Direct dependency | SHA-256 |
| --- | --- |
| `CurrentCellConstruction2011` | `03344f81c7817f625633470218727176f975ee7617154589534a0b94feb9bd0a` |
| `CurrentCellCoordinate2011` | `6e316a7a9a0107e8bc2bc41bf2bcd5868251b297f0b5cd7c79b64a52da1e9f48` |
| `WangTiles942Periodic` | `b426e06571ddc25095a0573784d2f289f116cb976468f826da128a4bb9713d53` |

The coordinate dependency's `CurrentCellCycle2011` source is
`874a68dc11255170f19dc1a5345e195f36379711f8af630b16dd6eb9fe77081d`.
I authored the earlier periodic-language module and several generic mask and
carry dependencies; I did not author this reviewed word assembly or the
coordinate/cycle equivalence. The fresh replay below covers only the two new
sources. Existing prerequisite objects were reused, not rebuilt or overwritten;
this receipt does not claim a fresh replay of their entire closure.

## Mathematical and interface findings

The definition extracts the tile index from `k.val / 2011` and the local field
from `k.val % 2011`. Slots 977 and 1004 use separately supplied dummy and marker
maps; every other slot uses the actual `localDigit (a j)`. The two control maps
are not silently equated or inferred from a tiling. Booleanity needs only their
individual bounds; support holds without those bounds.

`base_add_val` proves the full representative inequality from `j.val < N` and
`e < 2011`, including the final cell. Its field/index corollaries retain exact
representatives. `base_natCast` uses the scaled-modulus equivalence, so arbitrary
whole-period offsets are valid without a coprimality premise. The `N=1` case is
covered. The packet handles every local field and wrapped cell coordinate; it
does not establish correctness for an arbitrary binary rotation phase.

The local-data adapter excludes exactly the dummy slot in the range below 986;
marker 1004 is outside that range. Thus selector identity, the full complemented
label word and the exact selector payload are independent of both controls.
`word_selectorCount` uses the already-proved selection predicate and weighted
sum, rather than a new unverified enumeration. The selected physical position is
the existing proven permutation, and the actual weighted West/East orientation
is inherited unchanged from the reviewed cell packet.

The `Cell N` adapter identifies its base with the existing coordinate inverse;
it does not replace the digit function or assume an unproved relationship
between representatives. The origin formula is exactly the indicator of
`a 0 = 0`, and the marked specialization uses only `start_at_zero`. No unique-Start
premise is introduced.

`shiftedStartMarker` explicitly uses `a (j + stride)`. Its indicator criterion
and Boolean bound are proved. As its source comment and author receipt state,
this is not yet the temporal-copy correctness theorem; that orientation must be
proved when the constructed word is paired with the actual temporal kernel.
No matching, high-mask, carry, controller, rank or polynomial-existence premise
is hidden in any of these assembly conclusions.

## Isolated fresh replay

I obtained the pinned environment through `lake env`, put a temporary namespace
overlay first in `LEAN_PATH`, and symlinked unchanged prerequisite bundles into
that overlay. The two reviewed modules were excluded from those symlinks and
compiled freshly, sequentially, with the checks importing the new main object:

```text
lean -M6000 -j1 -o /tmp/current-word-construction-peer-6sb5cj46/DiophantineConsistency/CurrentWordConstruction2011.olean <absolute main source>
lean -M6000 -j1 -o /tmp/current-word-construction-peer-6sb5cj46/DiophantineConsistency/CurrentWordConstruction2011Checks.olean <absolute checks source>
```

Both frozen sources set `Elab.async false`. Both commands exited zero; the main
produced no Lean diagnostics. Main elapsed 4.02 seconds with peak 3272368 KiB;
checks elapsed 3.59 seconds with peak 3255916 KiB. Source hashes were unchanged
before and after execution. Both fresh objects are byte-identical to the
previous author-built objects.

| Fresh output | SHA-256 |
| --- | --- |
| Main `.olean` | `f8541db6af0c613bc9f05c5934d35b9edbadd1887220725644cd8d9ac44a3199` |
| Checks `.olean` | `96fdd67ea6959fb509e91e5fbd5dcb9cd5e166c25587ba1d4b3273935ed2cba2` |
| Main log | `dc3ff8ce6ade6de8ccecfeb9f14713b6410cf72475a095115a8075dc0c5fd983` |
| Checks log | `0f35f3ca6e97e997923226b097f91f7ea5a6dcbaff47a2fc7e7b12569807ef19` |
| `REPLAY.json` | `264525609340f1fb76c0b3d0af8b7ab1f4344fa4e4f1ffe3d5c5cdb29a07e6b2` |

Logs and the machine-readable replay receipt are in
`/tmp/current-word-construction-peer-6sb5cj46/`.
All 22 printed axiom reports contain only `propext`, `Classical.choice`, and/or
`Quot.sound`. The reviewed sources contain no `sorry`, `admit`, new axiom, or
`native_decide`.

The focused checks cover last-cell wrap, a complete-modulus offset, seventeen
periods at `N=1`, the copied-word identity at `N=1`, independent Boolean controls,
exact aligned-cell data, marked and non-Start origins, and the marker's explicit
addition sign. These agree with the public theorem scope.

## Smallest next scalar-mask construction

A useful next packet is the reverse low-mask implication. For the actual
constructed word `c`, Boolean controls and `a 0 = 0`, set
`C = NativeCyclicConvolution.word radix c` and prove `0 < C`,
`C < radix^(N*2011)`, and
`(C-1) &&& (lowPort*repunit width N+1) = 0`.
The existing `CurrentSparseDigits2011.low_mask_word` gives the exact mask,
including the origin increment. Zero the origin digit of `c`, use
`word_add`/`word_origin` to identify its scalar value with `C-1`, prove each
local digit mask from Boolean support, and use `mask_word_iff`. This needs no
carry or temporal-alignment hypothesis and supplies a missing reverse direction
of the existing decoder. The larger high-mask construction should separately
create normalized cyclic carries from the actual raw convolution; it must not
reuse a source-window theorem that already assumes the desired scalar F mask.

Only this new peer receipt was written. No frozen source, shared documentation,
compiled dependency, or git state was changed by this review.
