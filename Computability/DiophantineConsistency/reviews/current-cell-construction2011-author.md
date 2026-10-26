# Local tile-cell construction: author receipt

Date: 2026-10-26. Author: `controller_certificate`. This is an author
self-review, not an independent review. Both new files are frozen and
their final bounded Lean builds passed.

## Frozen files

Paths below are relative to
`Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

| File | Lines | Bytes | SHA-256 |
| --- | ---: | ---: | --- |
| `CurrentCellConstruction2011.lean` | 256 | 11054 | `03344f81c7817f625633470218727176f975ee7617154589534a0b94feb9bd0a` |
| `CurrentCellConstruction2011Checks.lean` | 107 | 4171 | `847c5e2b22d2c985419087a057c91d7db3238992e0ddc7c180af49e9bc154c7a` |

The main imports only `CurrentCellLabels2011`
(`88698cd0d678d788c169b22915594b9ce37dd5d5c19c3d0069b190e0575f740d`).
I also authored that dependency and the existing kernel and doubled-clause
arithmetic. I read the complete current labels, masks, kernel and clause
sources, the actual physical-position injectivity/range API, and sections
8–10 of `research/padding-staircase-independent/PROOF.md` before finalizing
this packet. The ordinary proof source has SHA-256
`69ce844ef80894251f4bd9510d9f60468585b4a004f4a624d3b347ce3e144fb8`.

The fixed mask source remains
`72ec99ac052c4d244f22f2590fb5645cebbe9ffe3a18fd89fe1cb8db7248fe06`;
the fixed kernel remains
`6f8642d8d3715335dcf61fb0060818226f227db24e126d4c14d58831e76d3a55`;
the physical permutation proof remains
`3351336105f22baf653dcefb3bd83273924dd539353eebf5f1232da855045cef`.
No frozen dependency was edited.

## Construction and proved interfaces

`bitDigit m j` is `m / 2^j % 2`. It is Boolean and equals the natural value
of the actual `Nat.testBit`. The generic reconstruction theorem proves
`binaryWord (bitDigit m) n = m % 2^n` by induction using the pinned Lean
core lemma `Nat.mod_pow_succ`; the bounded version reconstructs `m`
exactly. This works for any prefix length, including zero, without any
table enumeration.

For every actual `i : Fin 942`, `localDigit i : Nat → Nat` places one
selector at the proved `physicalPosition i`, and places the following
little-endian complemented colors:

| Physical positions | Width | Encoded value |
| --- | ---: | --- |
| 942–950 | 9 | `511 - (tile i).south` |
| 960–968 | 9 | `511 - (tile i).north` |
| 969–976 | 8 | `255 - (tile i).east` |
| 978–985 | 8 | `255 - (tile i).west` |

All other fields are zero, including dummy977 and marker1004.
`cell i : Fin 2011 → Nat` is its finite restriction. `cell_boolean` and
`cell_support` prove the Boolean and actual low-mask-support properties.
The four `localDigit_south/north/east/west` theorems expose each physical
bit pointwise, and `localDigit_at_physical` decodes every abstract selector
using the actual permutation, not a supplied sorting map.

`localSelected`, `localSelectorCount`, and `localSelectorPayload_eq` prove
the unique selected index, count one, and exact payload
`1 + packedTile (tile i)`. `localBinaryWords` reconstructs all four colors
in their true packed order. `localCopiedWord_eq` then proves

```text
localCopiedWord i = 2^34 - 1 - packedTile (tile i).
```

The unsigned subtraction is justified by the actual tile-color bounds.
Consequently `localPayloadBalance` is exactly `2^34`, and
`cellClauseBalance` gives

```text
2*selectorCount + 2048*(selectorPayload+copiedWord) + localDigit i 1
  = 2^45 + 2 + localDigit i 1.
```

The bare selector1 contribution is retained. `cellClauseMasked` proves
this value passes the full clause mask and is below radix `2^47`.
This is a local clause value identity; it does not claim that every
global incoming carry or temporal contribution has already vanished.

`localDigit_origin` says the local origin is one exactly for abstract
Start index zero. `literalStart` gives the actual finite origin bit, and
`startLabelWords` gives West253/North76/East252/South510 from the literal
Start tuple `(2,435,3,1)`.

The public compatibility helpers `copiedWord_of_local`,
`selected_of_local`, and `selectorPayload_of_local` reuse the existing
cyclic definitions. Their only data-binding hypothesis is equality with
`localDigit i e` for `e<986` and `e≠977`. They leave the safe dummy and
the shifted marker unconstrained. Their premise is an explicit pointwise
function equality to discharge when the global word is assembled; it
is not a native equivalence or calibration assumption.

This packet does not assemble a full `ZMod (N*2011)` word from a marked
tiling, place the shifted marker pattern, normalize cyclic carries,
prove all high-mask tests, construct the rank controller, or construct
a positive polynomial witness. Those remain separate steps.

## Builds and checks

I read all new code before execution and reread both complete final
sources after the last edits. Builds were sequential under the pinned
Lean 4.32.0 toolchain with `Elab.async false` and `-M6000 -j1`:

```sh
lake env lean -M6000 -j1 \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentCellConstruction2011.lean \
  -o .lake/build/lib/lean/DiophantineConsistency/CurrentCellConstruction2011.olean
lake env lean -M6000 -j1 \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentCellConstruction2011Checks.lean \
  -o .lake/build/lib/lean/DiophantineConsistency/CurrentCellConstruction2011Checks.olean
```

The final main build exited zero in 5.67 seconds with peak 3281404 KiB,
and emitted no Lean diagnostics. The final checks exited zero in
3.51 seconds with peak 3258436 KiB and fifteen standard-only axiom
reports (`propext`, `Classical.choice`, `Quot.sound`). No new axiom,
`sorry`, `admit`, or `native_decide` occurs.

The checks cover empty and truncated binary prefixes; actual selector
selection through the physical map; zero dummy/marker and absent-field
values; the distinguishable Start West/East low bits; Start South bits;
the complete clause mask; binding to the existing cyclic definitions at
`N=1`; and invariance of the copied word under arbitrary values in the
two separate dummy/marker slots.

The first main attempt exposed elaboration issues in a modulo-one base
case, rewriting an `if` condition with its decidability instance, and an
unannotated natural index inferred as `ZMod`. These were corrected
without changing the mathematics. The next main build passed. I then
weakened the cyclic binding hypothesis to exempt dummy977 and marker1004
and added the public payload helper; the final main build passed. The
first checks needed an explicit `decide` to close one small numeric
remainder goal. The final checks also include the free-control-slot test.

| Object | SHA-256 |
| --- | --- |
| Main `.olean` | `6c3b6096cd8089db4fdfdcf5140c84781f1a719c0dc6defe69f67af8c62e38b4` |
| Checks `.olean` | `219a36d9318a95fcb5c4ad3946e1ea6bb7a4f94750c7214d6d3612157c30ed70` |

The following logs include the separate timing summary as well as any
Lean output.

| Log | SHA-256 |
| --- | --- |
| `/tmp/current-cell-construction2011-main-stage1.log` | `fb63cf9c28ab21380f191713b35be25f4297c9774767032205ed6da889f56511` |
| `/tmp/current-cell-construction2011-main-stage2.log` | `ca90c714312b13aa48a93f48d00ca34ceb6cc0371ec88c2ce8d638d5f3205610` |
| `/tmp/current-cell-construction2011-main-stage3.log` | `2e87aa315683b4593bf707849fa97dfef435e507039aa4a117f77d17a10514f4` |
| `/tmp/current-cell-construction2011-checks-stage1.log` | `f24efd207083a1f708aa23de2fc6b662322407718fc43b595efac9b7b69839aa` |
| `/tmp/current-cell-construction2011-checks-stage2.log` | `8c2427e8281ad7c141dd659dd4d30dc6834375a3c97c1f0709d4c68fbeb2a4c2` |

Only the assigned new module, checks, and this author receipt were added.
No frozen source or shared documentation was changed, and no git operation
was run.
