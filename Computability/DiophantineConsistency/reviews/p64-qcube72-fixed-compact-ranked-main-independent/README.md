# Independent review of the fixed compact ranked-main result

**PASS within recorded direct captured-provider scope.** The no-Lean
`check.py` checks the successful outer and child exit reports, terminal and
retained source, runner and object, compiler log, result, process receipt,
all recorded guards, and both recently checked provider objects against
their producer receipts. The third direct provider,
`CompactSymbolicMaskData`, is pinned as a captured object, without a new
source-to-object or transitive reconstruction. The theorem's axiom report
contains only `propext`, `Classical.choice`, and `Quot.sound`. This is not a
Lean replay; dynamic, between-sample and transitive ancestry remains inherited.

The theorem assumes an `IΣ₁` model and an actual positive zero of the
72-graph at fixed symbolic compact ports
`(betaNat,K,lowNat,betaNat+highNat)`, where `K` is an arbitrary natural
number. It concludes both positivity and the quartic window for the generic
rank and existence of the main Pell coordinates at the auxiliary-norm rank.
The checker compares their two pinned Lean definitions byte-for-byte: both
are the same natural-model expression. In addition, the previously checked
`FreeMainWindowRankedMain` bridge applies `change` to the generic-window rank
using the auxiliary rank as `R`; Lean's successful acceptance provides
definitional-equality evidence for those imported definitions. This audit did
not rerun Lean, and its provider ancestry limitations still apply. A local function equality identifies the
opaque compact-port wrapper with the symbolic tuple, and the captured static
mask-data theorem supplies the exponential identity and both inequalities
required by the symbolic-port client.

The theorem does **not** establish the first-index congruence, the 72-to-76
reverse witness map, a consistency equivalence, or an iPRA endpoint. The
source's “source-only” comment predates the successful attempt and is
retained byte-for-byte. The checked direct project providers are reviewed in
the [compact rank-window review](../p64-qcube72-compact-rank-window-independent/README.md)
and [symbolic ranked-main review](../p64-qcube72-symbolic-ranked-main-independent/README.md).

Run while captured temporary provider paths remain available:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-qcube72-fixed-compact-ranked-main-independent/check.py
```
