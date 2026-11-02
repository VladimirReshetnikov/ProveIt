# Independent compact selector-divisibility audit

The read-only [audit](audit.py) of `a44a25113d` exited 0 in session 8751;
its [receipt](CHECK.json) and [terminal observation](terminal-observation.json)
record both matching source/seed/object/log chains, every inherited overlay
object, direct imports, child and outer exits, and a successful rerun of the
selector parent audit. No Lean compile was rerun. The axiom report per side
lists `propext`, `Classical.choice`, and `Quot.sound`, without warnings or
`sorryAx`.

For arbitrary model n and P, the theorem assumes `n < 2^10` and
`NoCarry(n + 2^10*P, 2^51 − 2)` and concludes both `n ≤ 1` and
`2^41 ∣ P`, using model operations. These premises are not derived from the
actual graph, and the theorem does not bind the compact payload or calibrate
the checker. The failed exploratory attempt is retained and is not successful
proof evidence.

The inherited providers lack a complete printed axiom inventory; Foundation
outer-wrapper and package-transitive/dynamic ancestry qualifications remain.
Resource measurements are sampled. This is not an iPRA proof. Merge
`f6ad1e00b1` later added three thirteen-variable sources that are not inputs
to this frozen pair.
