# Adaptive unit factors: independent review

26 October 2026. PASS, with no mathematical or source correction requested.
Root authored the 73-line main and 28-line checks. The controller reviewer
read both complete files, the author driver/receipt, the imported unit
classification, and the source/object boundary before independently replaying
the two leaves. This is independent review of the new factor packet; prior
collaboration on native carrier modules is not a new review of that full closure.

The four definitions retain the literal discriminant a²+4a+3 and multiplier
q³(q−1), over arbitrary signed integers. Modulo 4, the multiplier's square is
0, the discriminant is 0 or 3, and S=(a²+4a+3)(f²−1) is 0 or 1. Hence the
first factor is 1 plus a square; the main factor is 1+D² minus either 0 or a
square; the strong factor is 1+I²−S; and the auxiliary factor is one square
(V² if S=1, y² if S=0). None can be 3 modulo 4. The casts use ring operations
on integers, including signed subtraction; the finite `decide` proofs are
kernel checked, not native computation or an arithmetic truth premise.

The product proof correctly groups the other factors into the second integer
unit, excludes −1 for the first three factors, and obtains the fourth from
the remaining equality. The separately exported fourth exclusion is valid.
The reverse implication substitutes four actual unit equalities. There is no
positivity, Pell equation, source restoration, port calibration, or HA premise.
The focused controls deliberately include zero and negative factor values.

Frozen source hashes:

- Main: `b9bc1883c478f5e236c32b7d06ab4d132a80b3fd55e317df0650e55c497447cb`.
- Checks: `4ba76919056b926309c3a914b54c4a488bdc363775eacfdc6e4b6774e672ec98`.
- Author replay: `be118b13e49d8c55ddeab16b010a973c99280264297ed2f11d6736ba07edd2de`.

Independent fresh builds passed in 4.725s and 2.680s in
`/tmp/native-adaptive-unit-factors-controller-peer-0tr530p5/lib`.
The main log is empty. All five axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. Both output objects are byte-identical
to the author's pinned objects: main `50287a90e3309ce90c28cfa0eaca01683cee972e9cdfc10909cb25602ec80b3c`,
checks `48d8578042c2536945b0e5457f7101fa22bac0aa4f0e95953e0ee9459459eea2`.

The private overlay reused exactly 25 cached custom modules, no Foundation
modules, 22 direct external boundaries and 66 external companions. All 1,523
inherited observations plus ten peer-specific pins were rehashed before and
after execution; current import lists agree with the pinned closure. The nine
author evidence files and originals were checked. External LEAN_PATH entries
are package caches and the pinned standard library, without the shared project
object cache. Both new outputs are regular files. Commands use Lean 4.32.0,
`-M6000 -j1 -DElab.async=false`; the 512 MiB reserve held before both invocations.
No dependency was rebuilt and no accepted source/object was overwritten.

One initial peer preflight stopped before invoking Lean because my standard-
library suffix guard omitted the `leanprover--` component. Its driver and
unused private cache are preserved. Comparing against the actual pinned
compiler's standard-library path fixed that guard. Neither Lean invocation
failed, and no source change was made.

[Peer replay](native-adaptive-unit-factors-peer-replay.json) and its
[evidence manifest](native-adaptive-unit-factors-peer-replay/FILES.json)
preserve inputs, both source snapshots, commands, timings, logs, object hashes,
the preflight failure, and final pin checks. This review establishes only the
signed unit extraction packet, not a complete adaptive equation equivalence
or an HA proof.
