# Exact cyclic carry input for a constructed word

`CompactWordCarryJoin.word_carry` instantiates the previously checked
symbolic cyclic-product carry construction with the actual represented word
from definable `row` and `dummy` functions. For positive length `N`, the
word's size and global digit cap discharge the carry construction's word
hypotheses. The theorem still explicitly assumes the temporal contribution
`T < 2^(67*8807*N)` and retains it, together with all other-band, bare
rotation and incoming-carry terms, in the exact modular product. It does not
identify `T` with the required temporal multiplication, prove the product or
high-mask conditions, construct a graph zero, or yield an iPRA derivation.

The first bounded author attempt failed due to an omitted namespace, a
numeral normalization mismatch and a heartbeat timeout while unfolding a
large constant; its source and compiler log are retained. The corrected
second attempt locally makes the large symbolic constants irreducible and
exited 0 without warnings or `sorryAx`, with unchanged sampled direct
dependency and companion guards. Its axiom report lists only `propext`,
`Classical.choice`, and `Quot.sound`. The source, runner, logs and terminal
receipts are retained; package/transitive/dynamic and between-observation
provider ancestry remains inherited, and `/tmp` paths are ephemeral.
