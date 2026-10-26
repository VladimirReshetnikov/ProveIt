# Constructed copy and shifted-marker masks: author receipt

Date: 2026-10-26. Author: `circuit_reduction`. Frozen after full self-review
and fresh capped main/check builds. This is an author receipt, not a peer review.

## Sources and dependencies

Source paths below are relative to `Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

| File | Lines | Bytes | SHA-256 |
| --- | ---: | ---: | --- |
| `CurrentWordCopies2011.lean` | 217 | 12222 | `61e1662e3bd9a4a1409a5d47da4a017e714173ca3b2fc247a1bbb38a56546a9e` |
| `CurrentWordCopies2011Checks.lean` | 99 | 4581 | `a12cbec6f9889336a0b8add70c5a175f0c451c0b22bbbf7c81b552ff4b16c47c` |

The main has exactly two direct imports:

| Import | SHA-256 |
| --- | --- |
| `CurrentWordClause2011` | `df93b7dc684693e23097e5bfdba9aa3a9121595574b6026832d2a4f3f2fd24dc` |
| `CurrentAdjacency2011` | `160cef12e27cda2ece581ba0acfb2fcbbf194d918fe75d630705a7feb8e97133` |

Relevant unchanged dependencies are:

| Dependency | SHA-256 |
| --- | --- |
| `CurrentWordConstruction2011` | `9455d6c2015906a8f76ff2be5275a95cae5340f0ca3e8dc16666ffc6bab2b5b8` |
| `CurrentCarryConstruction2011` | `6efd60cd1ce0f40aa48e68ec7d9c2b2c680bbdc0aa289488c268e79fa68a026a` |
| `CurrentCellConstruction2011` | `03344f81c7817f625633470218727176f975ee7617154589534a0b94feb9bd0a` |
| `CurrentCellCoordinate2011` | `6e316a7a9a0107e8bc2bc41bf2bcd5868251b297f0b5cd7c79b64a52da1e9f48` |
| `CurrentCopyParity2011` | `dc49658f1d9c448eca9ff969336cd5f64b4f64483b47b48d72f3a6bd0d928c8a` |
| `CurrentPhaseParity2011` | `3abd1bc07fe430892871e13b0b066a689ef74854a45bc725ee73bfe349325eb7` |
| `CurrentReflectedGeometry2011` | `268ecac628932a93d79593ae0b4e1c8819817db58f27ec9613c4ad23a29d60c1` |
| `WangTiles942Periodic` | `b426e06571ddc25095a0573784d2f289f116cb976468f826da128a4bb9713d53` |

I read the ordinary construction and mask arguments in sections8–9 of
`research/padding-staircase-independent/PROOF.md`, the actual word/clause/carry
interfaces, the exact field-coordinate translations, and the existing literal
copy/marker convolutions and masks before implementation. I authored the earlier
CopyParity, ReflectedGeometry and Periodic modules. The new packet reuses their
exact arithmetic identities; no frozen source was modified. Existing compiled
prerequisites were reused, not freshly rebuilt for this packet.

## Exact construction and conclusions

`constructedWord a dummy s` is definitionally the existing actual word with
marker map `shiftedStartMarker a (s : ZMod N)`. Thus its marker in cell j is the
indicator of Start at j+s; the independent dummy map remains arbitrary except
where Booleanity is required for normalized carry bounds.

`base_sub_stride` proves the exact full-word identity

```text
base(j-s) = base j - cast(2011*s).
```

It uses the existing coordinate inverse and scaled-modulus translation. There
is no bound on s, inverse of2011 moduloN, or coprimality assumption.
`word_shift_at_base` and `word_shift_data` then retain the actual cell and field
when subtracting this full physical stride, including wrap through multiple
periods.

The pair identities are derived from actual tile matching, not supplied as
assumptions:

- `south_pair` uses the exact South942+j and North960+j local bits and the
  marked temporal equality at j and j-s, for all nine bits.
- `horizontal_pair` uses the exact current East969+j and preceding-cell
  West978+j local bits and marked horizontal matching, for all eight bits.
- `marker_pair` proves the temporal source equals the current selector0 bit,
  because m(j-s)=Start((j-s)+s)=Start(j). It needs neither tile matching nor
  a Boolean dummy premise; in particular it retains zero stride and N=1.

`normalized_low_digit` proves that the actual normalized digit equals the
complete raw convolution-plus-rotation at every field1..1004. Both outgoing
and incoming carries are derived using the established low reset theorem and
physical one-selector count of the constructed word. Neither a carry-zero
premise nor a mask test is given.

The three mask theorems use the actual high-mask digit1 and literal convolution
at every target. All reflected contributions are retained, then eliminated
modulo2 by their proved evenness. The nine temporal tests sum equal Boolean
South/North bits. The eight horizontal tests sum equal East/West bits and have
no temporal source because those field residues are unsupported. The marker
sums the current Start bit with its proven temporal copy. Each result is an
actual `digits k &&& CurrentHighDigits2011.maskDigits k = 0` statement.

`copy_masks` combines all17 copy tests and the marker test for the same given
bounded normalization. `exists_copy_normalization` constructs that normalization
using the actual finite cyclic carry theorem, then proves all18 tests. Its only
substantive inputs are `MarkedWord N (s:Integer) a` and an independent Boolean
dummy map; it asks for no carry solution, copy equality, mask, clean boundary,
unique Start, nonzero stride, or native source/polynomial solution.

The construction and exact marker APIs preserve zero stride and N=1. This does
not assert that an actual marked tiling exists for those parameters; their
marked matching premises are still present in the copy theorems. Padding,
cell-origin tests, top resets, the complete global high mask, controller rank
selection and polynomial existence remain outside the new conclusions.

## Fresh bounded checks

I read all new code before execution and reread both complete final sources
after the last change. Final commands, using the pinned Lean4.32.0 environment,
were sequential:

```sh
lake env lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentWordCopies2011.lean -o .lake/build/lib/lean/DiophantineConsistency/CurrentWordCopies2011.olean
lake env lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentWordCopies2011Checks.lean -o .lake/build/lib/lean/DiophantineConsistency/CurrentWordCopies2011Checks.olean
```

Both sources set `Elab.async false`. Final main exited zero with no Lean
diagnostics in5.30 seconds, peak3280608KiB. Checks exited zero with no warnings
or errors in3.98 seconds, peak3261388KiB. All14 printed axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`. No final source contains `sorry`,
`admit`, a new axiom, or `native_decide`.

Focused checks cover arbitrary whole-period shifts; N=1 with17 periods; the
independent dummy's j-s source; zero-stride marker equality; an unrestricted
non-Boolean dummy for the purely exact marker identity; and a concrete ZMod3
sign challenge. In that challenge the correct marker's actual temporal source
is1, whereas the same source with the opposite marker sign is0. No tiling is
asserted for that test function. Symbolic checks bind both actual physical color
orientations and instantiate the constructed-normalization endpoint without any
mask or incoming-carry premise.

The first main attempt required unfolding the word abbreviation at two rewrite
hypotheses; it also prompted removing two unused section-instance assumptions.
The revised main passed, and adding the existential endpoint passed on its first
build. All focused checks passed on their first build. No theorem was weakened
to assume a copy or mask conclusion.

| Output | SHA-256 |
| --- | --- |
| Main `.olean` | `71b9a3acbb1e3d5fa6507a5c56777cb11a818870da11876b6689034d5bf077ab` |
| Checks `.olean` | `00eaa4d598ac297db4e93c627a2b6214bf36763274e90917f0efde1b0592e64b` |
| `/tmp/current-word-copies-main-stage3.log` | `bbdea76f380ef65ddbd6ad34f42ce7f74b4100699978a263983959c1dacee53f` |
| `/tmp/current-word-copies-checks-stage1.log` | `dcf0e117b0f756dfafbe188c653c3f7643ed1de2d34ba4415cb6e3625cf3d1c7` |

Only these assigned new sources and this receipt were added. No frozen source,
shared status document, or git state was edited.
