# End-around carries with individual digit caps

The source generalizes the paired `compact44-scaled-end-around-prototype`
from a single common cap to a separate model-natural cap `D i` for each word
in an **externally finite** family. Given positive word length and modulus,
words below their word radix, digit bounds `dig w (X i) k ≤ D i`, a remainder
below the modulus, the explicit weighted-sum congruence, and

```
(∑ i, a i * D i) + 1 ≤ (b + 1) * (2^w − 1),
```

it constructs end-around carries bounded by `b` and proves the carry and
digit equations at every model position. The central new estimate applies
the existing all-model scaled remainder theorem to each word separately and
sums the resulting weighted bounds. Thus a single fractionally rotated word
may receive a large cap without imposing that cap on every other word.

This is a conditional `IΣ₁`-model result. It does not prove the actual
compact44 words satisfy these hypotheses, bind K or MC, establish the
fractional-rotation geometry or a clean predecessor, simulate a machine, or
construct an iPRA proof. The potential application additionally needs an
explicit model decomposition of the graph transport equation and a verified
weighted mass bound. The finite half-radix result in
`compact44-fractional-clean-column` is not an all-model fact.

Exploratory Lean session 6078 actually exited 0 with four expected axiom
reports and no warnings. The paired replay was run as:

```
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-heterogeneous-carry-prototype/replay.py --output /tmp/ipra-compact-heterogeneous-carry-pair-01
```

Its outer session 69417 actually exited 0. Both children exited 0, their
objects and four axiom reports matched, and the separately audited 24-module
window provider was checked before and after; see `evidence`. Both reports
list Lean metatheory `propext`, `Classical.choice`, and `Quot.sound`, and
neither contains `sorryAx` or warnings. The paired scaled-digit parent is
independently audited. This packet itself awaits an independent audit; the
inherited provider does not have a complete printed axiom inventory, and
package-transitive and dynamic ancestry are not fully authenticated. The
reported memory values are samples, not hard process-tree quotas.
