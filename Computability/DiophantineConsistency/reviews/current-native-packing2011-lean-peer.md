# Independent review: coherent current native packing

Verdict: **PASS**, no requested source change. I read the complete frozen main
and checks, followed all three direct interfaces, and freshly replayed the two
targets in an isolated overlay. The packet constructs one coherent source,
normalization, mask pair, repunit window, and stated positive scalar witnesses.
It explicitly stops short of the printed-rank temporal equality and full
31-variable source-system solution.

Root authored the reviewed composition. I authored its earlier copy/padding
support and parts of the geometric construction, including BandMarker and
TraceCycle/Boundary, and separately reviewed the complete high-mask composition
and word/top-bound interfaces. Those prior roles are disclosed; I did not
author this packing source or its checks.

## Source and dependency bindings

Paths are relative to `Computability/DiophantineConsistency/`.

| File | Actual lines | SHA-256 |
| --- | ---: | --- |
| `Lean/DiophantineConsistency/CurrentNativePacking2011.lean` | 94 | `df17b8a5c2913b2ffec6d4b6fbd3fe5127aa45e76273ed88734f30da548fa92e` |
| `Lean/DiophantineConsistency/CurrentNativePacking2011Checks.lean` | 54 | `2824c983a18897a8262135b82dc540b00a46486ca3c1abff2308ae53eb61d4d7` |

The source hashes match the author's freeze notice exactly. The notice's
105/58 line counts were stale; the actual files contain 94/54 lines. This is
a metadata correction only and was reported to root.

All direct imports were read in full, including the newly composed scalar and
power-dimension sources. Their existing proof objects were reused, not freshly
rebuilt in this replay:

| Module | Source SHA-256 | Reused `.olean` SHA-256 |
| --- | --- | --- |
| `CurrentWordHighMask2011` | `f14b90ec3d4210c75dce2e4ece4de6f50bb1b2069e26b9329309eadd1c7da74a` | `75b5ca288ad3d4b3cb64abc2935f1b0c24e99ea8e4ac50b01e373f4e289f66b8` |
| `CurrentWordScalarWitness2011` | `8a644c7eb65bff5016d28a992e2db477bb5341b33fa31e92f1a086a0d0e4879e` | `5789a6252546bb394ccf0d84239cde81023d83ebd6d106eac24f23a3c672ed2b` |
| `WangTiles942PowerDimensions` | `1021a39e8106c9a493986ee72aa0d2f85addff0a2d3ee822ca44a8a6441ae283` | `10c0788be4c85e0d5951ddd4e6c846c8a5a60c75f4c6e24c73aeb9eb60f02545` |

I also read the scalar-witness author receipt, the independent power-dimensions
review, and the root's complete native-mask construction review. This is not
a new replay of the machine, table, geometry, or full dependency closure.

## Exact mathematical scope

`repunit_pos` retains the origin term and uses only `N>0`. `repunit_balance`
is an ordinary natural equality, not a congruence:
`beta * repunit width N + 1 = radix^(N*2011)`. The geometric-sum proof keeps
the actual width `47*2011` and the exponent orientation; the equality theorem
also permits `N=0`, while positivity correctly does not.

The `Facts` record binds every conclusion to the same `a`, dummy map, stride,
carry function, and normalized digits. The source is exactly
`constructedWord a dummy s`, with marker
`shiftedStartMarker a (s : ZMod N)`. Its scalar fields are the literal packed
source and normalized word, with `alpha=q-C-F` and
`z=((K+w)*C)/(q-1)+1`. The source recovery identities, strict slack, positivity,
and actual transport factor equal to 1 come from that same normalization.
Neither mask comes from a different existential choice.

`marked_constructs_packing` first obtains the actual high-mask normalization,
then derives scalars and the low mask using only the Start-at-origin projection
of the same marked word. Both literal masks keep their origin adjustments:
`(C-1) &&& (lowPort*J+1)=0` and `F &&& (highPort*J-1)=0`. No mask, clean-carry,
positive representative, scalar balance, quotient equation, or desired
transport identity is assumed. The dummy map is an independent arbitrary
Boolean map, including the uniformly enabled map tested by the checks.

`halt_constructs_power_packing` starts from an actual finite halt of
`DecimalMachine215.machine`. For any natural base `p>1` and independent lower
bounds, it preserves the actual marked word at modulus `p^rw*p^rh`, stride
`p^rw`, and the exact equality `p^rw*p^rh=p^(rw+rh)`. Unique Start is retained
from the canonical geometric construction, not assumed. The local nonzero
instance is proved from `p>1`; no hidden coprimality or rectangularity premise
is inserted. Primality of `p` is not needed for this geometric endpoint.

The multiplier remains `w=2^(47*(2011*s))=(radix^2011)^s`. It is chosen from
the tiling stride. This packet does **not** equate it with the value forced by
the printed rank, choose safe dummy subsets, or fill the remaining Pell/source
coordinates. It consequently does not yet assert a positive polynomial zero
or the complete equation converse. The source-level scope statement is accurate.

The checks preserve the single-cell repunit, ordinary two-cell balance, the
same-word scalar/mask existential, uniformly enabled dummies, and the complete
cofinal power-dimension endpoint. An actual `MarkedWord` at `N=1` cannot exist
for these tiles; the N=1 check here correctly concerns the repunit identity,
not a spurious one-cell tiling witness.

## Isolated fresh replay

Both reviewed sources were read and hash-checked before execution. The overlay
`/tmp/current-native-packing-peer-m8zfc6sv` excluded both reviewed target stems
and symlinked unchanged prerequisites. Main and checks were rebuilt sequentially
with the overlay first in `LEAN_PATH`:

```sh
lean -M6000 -j1 -o /tmp/current-native-packing-peer-m8zfc6sv/DiophantineConsistency/CurrentNativePacking2011.olean /home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentNativePacking2011.lean
lean -M6000 -j1 -o /tmp/current-native-packing-peer-m8zfc6sv/DiophantineConsistency/CurrentNativePacking2011Checks.olean /home/codex/.codex/worktrees/46be/Proofs/Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentNativePacking2011Checks.lean
```

Both passed. Main took 3.30 seconds, peak RSS 3,364,144 KiB; checks took 2.81
seconds, peak RSS 3,330,992 KiB. Main emitted the disclosed symbolic
exponent-2011 threshold warning; it did not fail or leave an obligation.
Checks had no warning. All four axiom reports use only `propext`,
`Classical.choice`, and `Quot.sound`. There is no `sorry`, new axiom, or
`native_decide` in either reviewed source.

Both sources remained unchanged. Both fresh objects match the author's
announced hashes and are byte-identical to the shared frozen objects. No
shared object, source, documentation, or git state was modified by replay.

| Artifact | SHA-256 |
| --- | --- |
| Main fresh `.olean` | `c4db44f3f25392cf34228e9e5be1ced95938d6373737ddccd6abd1650151543d` |
| Checks fresh `.olean` | `9b5c0e97f2180b4cf35b861acbaae9a1333f7effd36b05471bc268832d6d65a6` |
| Main replay log | `61d5ab7ff39d6cb2770728d20f3bcf337c738412af265b80a5516c3eb80ec49f` |
| Checks replay log | `6b10cda310859dbf3f3196bda96445de2e8125af4bc03f8babf082bb67124b48` |

Complete commands and unchanged-source flags are saved in
`/tmp/current-native-packing-peer-m8zfc6sv/REPLAY.json`.
