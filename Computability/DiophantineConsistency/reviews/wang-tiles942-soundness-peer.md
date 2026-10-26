# Independent review: marked Wang word forces actual blank-tape halting

Date: 2026-10-26 UTC. Reviewer: `controller_certificate`. Result: **PASS**;
no correction requested to the frozen packet.

Root authored the reviewed Soundness module/checks and the RowEncoding,
OperatingRow and StripGeometry compositions. The reviewer authored its
RowStep dependency and the earlier InitialHorizontal, InitialStrip and
ResetRows modules. Circuit authored the actual language, periodic-plane
and signal modules; complemented authored the operational color/action
and head-bound lemmas. This is an independent review of root's new
soundness composition, including its application of those prerequisites.
It is not an independent-author or fresh-closure claim for the entire
proof chain.

Exact frozen bindings, relative to `Lean/DiophantineConsistency/`:

| File | SHA256 |
| --- | --- |
| `WangTiles942Soundness.lean` (71 lines) | `7380edb40832cc974606eddd2651b9b765712ac9bdb55cdb1ae1e7a83d450068` |
| `WangTiles942SoundnessChecks.lean` (47 lines) | `4dac8e30913ab909a88c6c648fa20595f016d758866f359232ac3166845e53c8` |
| `WangTiles942RowStep.lean` | `f4b6f60e4dece143de6d45120c8aa8ae84691d50b1b888e6e0dcb0226f17f84b` |
| `WangTiles942RowEncoding.lean` | `d9c24628856b55b6e91b843208539982810d84fbb6f2b5882382b61f4a3cb9df` |
| `WangTiles942Periodic.lean` | `b426e06571ddc25095a0573784d2f289f116cb976468f826da128a4bb9713d53` |
| `WangTiles942InitialStrip.lean` | `b20872f398fc330069ba8eec137d295bc6f6418b6c215a53afcff6334128a100` |
| `WangTiles942StripGeometry.lean` | `2439e3e5bd3b9f4eeea38013e4a2e237444626cc5864b0244463be8a88ce4e7a` |

I read the complete target main and checks before execution. I re-read
the complete Periodic, RowEncoding, InitialStrip and DecimalMachineInitialization
sources for this review, and had read the complete RowStep, OperatingRow,
StripGeometry, HeadBounds, MachineEncoding, Action, Step and operational
Core sources during their immediately preceding implementation/review.
I checked the literal `KDenseBridge.BlankHalts` definition as existence
of an actual blank-run time with state `none`. No legacy layout theorem
or assumed native calibration is used by this composition.

`marked_halts_before_period` assumes only the actual `MarkedWord N s a`
and the nonempty cyclic modulus instance. That structure gives a Start
at index0 and the literal horizontal/time color matches; it does not
assert occupation, a machine run, cleanliness, unique Start, coprimality
or an existing rectangle. The stride `s` is an unrestricted integer.

The contradiction argument assumes no actual halt at any `t<N`, and
therefore obtains an operating state for each such time. It derives
the fixed strip and the actual configuration at clock1 from the marked
word. In particular clock1 is the real blank-machine first step, with
the written origin and adjacent state1 head; it is not a substituted
initial configuration or an off-by-one blank row.

The induction derives `RowEncodes` at times `k+1≤N` for exactly
`machine.run(k+1)`. At each successor step, the live-state premise is
used only at the earlier time `k+1<N`. The existing actual `row_step`
derives the next row and head containment without a no-finish premise.
No assumption that the state at timeN is still operating is required:
the last step may enter halt, and the encoding's color bound still holds.

Taking `k=N−1` is justified by `NeZero.pos N`; the natural subtraction
is not silently treated as integer subtraction. The initial strip's
`L>0` and `R≥2` put integer coordinate0 strictly inside the same fixed
strip at every time. Hence the row encoding at timeN gives north color
at most433 there. The actual plane has vertical periodN for every
stride, regardless of whether N is a least period. It follows that the
tile at `(0,N)` equals the marked Start at `(0,0)`, whose north color is
435. The explicit `435≤433` contradiction proves an actual halt strictly
beforeN. Repeated Start occurrences elsewhere play no role.

`marked_blank_halts` merely forgets the strict time bound and exposes the
repository's actual blank-halting predicate. It adds no machine or
consistency-equivalence assumption. The focused contrapositive excludes
marked words from actual nonhalting. The small-period check uses the
actual live configurations at clocks0 and1 and the strict bound to prove
`N>2`; it does not assume a least period or unique marker.

Independent replay used Lean `v4.32.0`, `-M6000 -j1`, and a new temporary
object namespace `/tmp/wang-soundness-controller-peer`. The namespace
symlinked existing prerequisites while excluding every main/check target
stem entry. The main was freshly compiled there, and the checks imported
that new object through the first-priority `LEAN_PATH` overlay. No shared
source or object was modified.

```sh
/usr/bin/time -f 'elapsed=%e peak_kb=%M exit=%x' lake env bash -c \
  'export LEAN_PATH="/tmp/wang-soundness-controller-peer:$LEAN_PATH"; exec lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942Soundness.lean -o /tmp/wang-soundness-controller-peer/DiophantineConsistency/WangTiles942Soundness.olean'
/usr/bin/time -f 'elapsed=%e peak_kb=%M exit=%x' lake env bash -c \
  'export LEAN_PATH="/tmp/wang-soundness-controller-peer:$LEAN_PATH"; exec lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942SoundnessChecks.lean -o /tmp/wang-soundness-controller-peer/DiophantineConsistency/WangTiles942SoundnessChecks.olean'
```

Both commands exited zero. Main:3.36 seconds,3195204KiB peak and no Lean
diagnostics. Checks:3.28 seconds,3194240KiB peak. All four printed axiom
sets contain only `propext`, `Classical.choice` and `Quot.sound`; no
custom, native-decision or `sorryAx` dependency occurs.

| Independent replay artifact | SHA256 |
| --- | --- |
| Timed main log | `d0599a4f04c6c102ad3c0719250e3434bed3b318411970f541d9a3835a2953ab` |
| Timed checks log | `c55240fd48047e5d0b2802324e30c6fc16fb74c2a795977e152b6a236a901a79` |
| Fresh main object | `6a4550aff183a0066e2f8d21d2df56bd3dee60384a468d0e5fa5758f6d0b0f86` |
| Fresh checks object | `cdd60187443f7a4f88c225934916c43dcd2624b1f84216afc6dcd49754edc7d6` |
| Source/object/toolchain input manifest | `20a9f5e05ef4ff08b6c147533fd6829ccee6e8435b6ec351a5fb339a3d03e264` |

The fresh main object is byte-identical to root's frozen main object.
There was no original shared check object; the checks were saved only in
the independent temporary namespace. All24 manifest inputs were rehashed
unchanged after replay. Existing dependencies were reused, so no fresh
full-closure compilation is claimed.

Scope: this proves the marked-word-to-actual-blank-halting direction for
the current literal 942-tile language. Connecting current polynomial
zeros to this theorem and then to the exact consistency statement is a
separate composition; the reverse witness construction and the full
equivalence are not established by this packet alone.
