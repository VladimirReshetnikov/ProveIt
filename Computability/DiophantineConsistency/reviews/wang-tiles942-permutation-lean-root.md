# The actual printed physical map is a bijection

Date: 2026-10-25. Author: complemented47_review. Independent complete
source/check review and fresh module/check replay: ROOT.

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| WangTiles942Permutation.lean | 3351336105f22baf653dcefb3bd83273924dd539353eebf5f1232da855045cef |
| WangTiles942PermutationChecks.lean | 8deab00aea2b9c05ae07deddec25a4ef7169bfd891da07ad601a32ee42d89ffe |

ROOT read all264 module and58 check lines before running either file.
Both fresh `lake env lean -M6000 -j1` runs exited0; the main log was empty.
All13 printed axiom reports contain only `propext`, `Classical.choice`,
and `Quot.sound`. The author also checked both frozen files freshly;
all four predecessor source hashes remained unchanged. This is a module
replay against checked prerequisites, not a full ancestor/umbrella rebuild.

A structural function recovers each original index from its tile colors.
Its family proofs cover all430 transitions, every signal and copy row,
Start, and every tail tile. The already-proved exact row index range
then makes the tile map injective. A generic mixed-radix argument proves
packed-weight injectivity within the true color boxes.

For bounded weights, each literal floor term is exactly the indicator
of a strictly greater weight. The physical rank is consequently one
plus the cardinality of the strict upper set on non-Start indices.
Nested strict upper sets give strict cardinal inequalities, proving
the range and injectivity of the actual printed map. Finiteness gives
surjectivity and an explicit equivalence of Fin942. Start stays at0;
the non-Start physical weights are strictly descending. No assumed
permutation, sorting array or quadratic pair-comparison cache occurs.

The focused checks include the actual initializer at504 and its inverse
928, unique preimages of every physical position and strict descending
weights. The auxiliary independent numeric reconstruction in the
[table peer receipt](wang-tiles942-lean-peer.md) agrees with the full map.

This closes the finite physical-permutation obligation. Coefficient-tail
and physical convolution bounds, phase/count recovery, native tile/machine
semantics and the complete consistency equivalence remain to be composed.
