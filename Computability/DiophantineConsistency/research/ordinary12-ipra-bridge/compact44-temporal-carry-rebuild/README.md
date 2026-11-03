# Guarded temporal carry-client rebuild

This rebuilds the previously checked
[`CompactTemporalConstructedCarry.lean`](../compact44-temporal-constructed-carry-prototype/CompactTemporalConstructedCarry.lean)
with only its first import adjusted to use the locally rebuilt top-level
`CompactConstructedCarryInput` object. It derives a cyclic carry input for
`((K + 2^e) * C) mod (2^(67*n)-1)` using a temporal rotation constructed
from `C`, assuming positive `n`, positive modulus, the source bound and the
source digit cap. The source's full inherited conditions and limits remain
as in the original prototype.

The bounded single-author run exited 0 without warnings or `sorryAx`; its
named axiom report contains only `propext`, `Classical.choice`, and
`Quot.sound`, and sampled direct dependency and companion guards remained
unchanged. The command, source/object hashes, dependency list and log are
retained. This is not a paired replay or a complete package, transitive or
dynamic ancestry audit; provider paths under `/tmp` are ephemeral.
