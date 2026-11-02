# Independent compact tile-payload bound audit

The read-only [audit](audit.py) of `cfeef02268` actually exited 0 in session
18830; its [receipt](CHECK.json) and [terminal observation](terminal-observation.json)
record the matched source/object/log chains, direct imports, recorded child
and outer exits, and a successful window-parent audit rerun. The report on
each side lists Lean metatheory `propext`, `Classical.choice`, and `Quot.sound`
without warnings or `sorryAx`. No Lean compile was rerun.

In any IΣ₁ model, the theorem assumes `w < 2^8`, `n < 2^9`, `e < 2^8`,
and `s < 2^9`, and proves `0 < v < 2^41` for
`v = w + 2^8 n + 2^17 e + 2^25 s + 127·2^34`, with the final power
interpreted internally. These are explicit assumptions on model elements;
the theorem does not bind them to any of the 943 table rows or prove that
the formula generates the actual literal coefficients. It also does not
derive graph no-carry premises, simulate the machine, calibrate the checker,
or establish an iPRA proof.

The parent providers lack complete printed axiom inventories; Foundation
outer-wrapper and package-transitive/dynamic ancestry qualifications remain.
Resource measurements are sampled. Merge `f6ad1e00b1` added three
thirteen-variable sources that were not inputs to this pair. The retained
first exploratory proof attempt failed; the author's corrected exploration
and paired replay are separate. The first independent script setup also
exited 1 immediately with a missing `Path` import; it was fixed before the
successful audit and started no Lean process.
