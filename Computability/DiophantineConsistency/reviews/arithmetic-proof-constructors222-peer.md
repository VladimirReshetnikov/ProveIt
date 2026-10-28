# C222 proof constructors: independent read-only review

26 October 2026. **PASS within the stated scope; no correction requested.**
I independently read all 126 main lines and 58 check lines, the complete
author receipt and replay metadata, and all three preparation/build/receipt
drivers. I reread the actual new row and history recurrence, old numeric
MP/GEN gate definitions, and actual KCode222 rule constructors. I did not
compile, execute those drivers, or edit frozen files. The recorded builds
and axiom reports below are the author's evidence, not my own replay.

| Input | SHA-256 |
|---|---|
| Main | `98f9d4e10727e493e721406c30b8c26d4e3b1253bae603fc3f51391090bc5ab8` |
| Checks | `29a69d732ba8d9dc11065a174dc16bb3283b9c30abcd075e89b1f99c3f6aa3b8` |
| Author receipt | `14f134d19c4d4cb78b25e39aa4531d95d30ebd05875a1a2cb907424324fc4119` |
| Replay metadata | `57981cb7b33003a917b600c67933d5c1bd24828513935ad0a6a1b42a01c20627` |
| Input inventory | `259db7e172574ab0c954a1b76fbf8aff9bf82a680be6e2c9dfb063247ba3f44a` |

The literal node is `12*payload+tag+1`. For `tag<12`, the proof derives
both division and remainder identities and applies only the actual
`ArithmeticHistory222.value_succ` recurrence. It does not assume a supplied
valid proof or a standard internal code. GEN uses the entire tail child;
MP uses its minor and major projections. In `value_mp`, the hypotheses
`value p=minor+1` and `value q=major+1`, together with
`major=wim minor conclusion`, supply the exact predecessor witnesses and
bounds of `ArithmeticRow254.MPGate`; no child validity gate is dropped.

The rule equations cover exactly the twelve actual tags. Tag 9 computes
growG with no side conditions. Tag 11 uses the helper-free bundle and
exactly `c≠a` and `c≠b`; `a=b` and `c=0` remain legal when these gates
hold, and either forbidden equality returns zero. The inherited numeric
rows are used only where unchanged. In particular, no old rho7 equation
is substituted for growG, and no old C254 history semantics is invoked.
The value encoding distinguishes rejection zero from accepted formula
`conclusion+1`: proof code 1 evaluates to 1 and therefore proves truth code
0, not false formula code 1. No theorem for tags outside `[0,12)` is claimed.

I rehashed all recorded source/object evidence, external roots, compiler,
manifest, parent receipts, drivers, source snapshots, run records, logs and
timing files: **588 hash comparisons matched**. The inventory contains
119 custom sources (95 Foundation), 404 object companions, 38 external
roots and six parent receipts. I independently reparsed every selected
source's imports and matched the recorded import lists. This validates
the supplied provenance, not a fresh transitive Foundation/package build.

The successful final pair uses private
`/tmp/constructors222-controller-lnq94s95`, compiler 4.32.0 and
`-M6000 -j1 -DElab.async=false`. Both final exit codes are zero, main
diagnostics are empty, and all 15 reported axioms are limited to
`propext`, `Classical.choice`, `Quot.sound`. The earlier rejected numeral
normalization run and unused-simp warnings are retained and correctly
separated; its unexecuted checks entry is not counted as a successful build.

I previously reviewed the new template/row/history/Nat-binding packets;
their author was the present packet's author. This review independently
checks the new constructor composition but does not repeat every imported
proof. It establishes no seed validity, inter-calculus interpretation,
machine runtime theorem or internal HA equivalence. Root's separate fresh
replay remains independent execution evidence.
