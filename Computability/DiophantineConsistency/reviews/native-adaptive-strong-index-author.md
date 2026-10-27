# Native adaptive strong-index author receipt

The new 200-line main and 49-line focused checks are frozen after a clean
private fresh replay. This is author validation, not independent review.
All final source and driver bytes were read before execution; the final
source delta is only removal of a redundant cast tactic. Existing proof
sources, shared objects and frozen proposal/cache files remain unchanged.

## Exact theorem scope

`strong_square_divisibility` uses `Jones1980.relaxed_aux` to derive
`f=xn_A(m)` and `p|m`. `Pell.y_dvd_iff` gives `c|yn_A(m)` and
`Diophantine.χ_sq` then proves `c^2|f^2-1`. This precedes the auxiliary
congruence and does not cancel the discriminant in the original norm.

`literal_index_of_strong` retains the exact integer graph values
`V=f^2*(c*T-R)-c` and `y=V+u`. The positive strong norm derives `f≥2`;
`T>0` and `c>2R` derive `V>c>0`, then `y>0`. With
`f^2-1=c^2*h`, it constructs
`j=f^2*T-R*c*h-1`, `o=f*(c*T-R)` and proves both positive and
`V=j*c-R=o*f-c`. These are conclusions, not source assumptions.
The literal auxiliary equation becomes the exact signed norm consumed by
`NativePellStepDown.source_index_of_strong`, yielding `p=R`.

`adaptive_main_index_exact` takes the original RankWindow positive
variables, `PortBox`, `beta≥15`, exact q/target/transport cuts and literal
A0/A1 zero equations, plus the positive f/i/T/u and literal `Fs=Fa=1`.
It derives the required classifications and bounds from RankWindow.
The result contains positive D, the exact Dstar quotient, both main Pell
coordinates at `R.toNat`, `c^2|f^2-1`, positivity of actual V/y, and the
two positive exact quotient witnesses. It preserves the supplied i and f.
The source multiplier J is unrestricted; StepDown's formal target
parameter J is instantiated with `R.toNat`, not that multiplier.
The high-mask port enters the target already shifted once.

The public wrapper has no supplied source certificate, Pell index,
oddness, positivity of V/y/j/o, or canonical-witness premise. The generic
helper legitimately exposes classification/size hypotheses, which the
wrapper discharges. The graph instance may set `k=eta+zeta`; the theorem
allows any positive k and retains the exact `c=kY+eta` cut.

The focused checks verify the quotient algebra, a concrete auxiliary
value, the actual graph's alternative Fa evaluation order, and a client
of the full literal wrapper. The packet does not bind every gate of the
whole product, restore the first index, recover X=2^R, discharge the
remaining free-J factor3 argument, restore a full source, or prove the
converse/current low-degree equation endpoint. No new operation/degree,
ConZFC or internal-HA result is asserted.

## Frozen pins

| Artifact | SHA-256 |
| --- | --- |
| `Lean/DiophantineConsistency/NativeAdaptiveStrongIndex.lean` | `6e0e0a65b62defe5759f54eeb9a527a48a5d7d8ffb35021187930acb44098284` |
| `Lean/DiophantineConsistency/NativeAdaptiveStrongIndexChecks.lean` | `21ce43789d9204678bed705b4d1004d7c7f42d87c970dae6fb710eb2d5acaf7b` |
| `reviews/native-adaptive-strong-index-replay.json` | `9cea61fc42223f1e98eef70bd3301b1becf2bffbc939cd74486b4148b54033ab` |
| `/tmp/native-adaptive-strong-driver.py` | `0f0e66bd42a3babe60259f8aca1308f9dd80c9c09a46b58b6a7f37209e563931` |
| `research/adaptive-strong-index2011-proposal.md` | `b7a7455b0162264c211345e61e3573d5bbc74e0486287e1b098b44d641c3c0ee` |
| `research/adaptive-strong-index2011-cache-audit.json` | `7af0cc253f39890be243192bdc7f427d0f4bd258835a8d641d312a02ed6b0055` |

The main imports only `NativeAdaptiveRankWindow`; the checks import only
the new main. The private closure reuses 29 authenticated custom
source/object pairs and exactly 22 external boundary names, including
implicit `Init`, with 66 external object companions. All 153 direct input
pins, actual custom import headers and import closedness were checked
before and after execution. This is inherited authenticated cache reuse,
not a new full dependency/Mathlib/Foundation rebuild.

The frozen plan's original provider remains explicit:
`/tmp/native-adaptive-window-o0wgi9j6/state.json`, SHA
`001e86fa696632dc69c2778a3c93ba687989b30c0541c5f1938650227ca4241a`.
Root subsequently accepted RankWindow at `6bebb630ba` and reported an
independent byte-identical main object. That later acceptance is recorded
without rewriting the frozen plan or silently changing providers.

## Final replay

Private directory: `/tmp/native-adaptive-strong-eknra1gh`.
Input manifest SHA:
`8759661de28a892fd03f48e24f8aa26e5c9c41a21a90ddde808509e0e17cef7a`.
Final state SHA:
`cfc7c1e36ee7817871f459a26678529d71b4a9aeecd9cb740d4d8f01cfebe350`.

The pinned Lean 4.32.0 commands used `-M6000 -j1 -DElab.async=false`,
sequentially, with a private `LEAN_PATH` plus exactly the authenticated
external roots. The shared project cache was absent from that search
path. The new outputs were initially absent and are regular nonsymlink
files; reused private input links were not mutated. No prerequisite or
Foundation compiler ran. The 512MiB reserve passed before each command
and after completion; packaging found 2,223,034,368 free bytes.

| Leaf | Exit | Seconds | Peak RSS KiB | Object SHA-256 |
| --- | --- | --- | --- | --- |
| Main | 0 | 6.929 | 3,260,128 | `1cccad885cab6b984150c7b8205f512d9243c53dbf71eea687cc1f3924cd1e77` |
| Checks | 0 | 2.897 | 3,214,456 | `1bbe2b6dbf3953a36c128e11cbf0307413c3bd92f34adaa5fb59a77544a84b54` |

The main log is empty. Checks produce exactly three reports, each limited
to `propext`, `Classical.choice`, and `Quot.sound`, with no warnings or
errors. The final sources, all input pins, every stored log/snapshot and
all successful objects were verified again before durable packaging.

## Complete attempt history

1. `/tmp/native-adaptive-strong-ylhjunx8`: main exit 1 after 3.007 s.
   Compact `0<i` was tokenized as an imported notation, causing three
   parser errors. Only spacing was changed to `0 < i`, including the
   corresponding focused client. Checks were not executed.
2. `/tmp/native-adaptive-strong-2jpbzxyl`: both leaves passed in 6.828 s
   and 2.897 s; all three axiom reports were standard-only. One redundant
   `push_cast` in the main triggered an unused-tactic warning.
3. `/tmp/native-adaptive-strong-eknra1gh`: removing that tactic produced
   the clean final pair above. No public statement, premise, resource cap
   or mathematical argument changed between attempts.

The durable replay JSON embeds 24 complete text records: the exact driver,
all three input/state records, all executed source snapshots, logs and
timing files, and the unchanged proposal/cache audit. Private binary
objects are identified by their hashes. Both the parser failure and the
warning-bearing successful attempt are preserved.
