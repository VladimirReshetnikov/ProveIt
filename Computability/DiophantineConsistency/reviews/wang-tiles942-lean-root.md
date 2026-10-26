# Binding the complete 942-tile table to the decimal machine

Date: 2026-10-25. Author: complemented47_review. Independent whole-source
review: ROOT and circuit_reduction. Independent full module replay and
numeric reconstruction: circuit_reduction; see its [peer receipt](wang-tiles942-lean-peer.md).

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| WangTiles942Data.lean | ac9047c705dddbab3bec84265beff2d72d498496bde12261cc76c46dc0c5a125 |
| WangTiles942Core.lean | 7471a9ff93f06d0eb39c2f3791d5db28dd2927e6346213173f38c2b3ea150d85 |
| WangTiles942.lean | 77be337f20089de1b8a5b795d0a61628e4334673d26f8100fc1500009ac28ea6 |
| WangTiles942Checks.lean | 6835a5280546f89b7e211378f9f8209c190b66a3c5680fc8e473b37585fd9aa3 |

ROOT read every source/check line before accepting the packet and freshly
ran the focused Checks file with `lake env lean -M6000 -j1`; exit0.
All15 axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`.
The author checked all four modules freshly, and the independent peer
replayed them against a temporary object overlay. ROOT's own replay was
the focused check, not a full replay of the three main modules or their
entire ancestral closure. Final frozen source hashes were rechecked.

The Data module binds every cached action to the actual715-digit machine
decoder in27 bounded kernel batches. Both target lists are proved to be
exactly the decoded target sets; all432 rail-cache entries are bound to
the full filtered target cardinalities. The halting target215 is retained,
and the formulas cover empty intervals and q outside the cache.

The Core defines every printed row family, proves the exact index range
0..941 and its permutation back to printed order, and derives tight color
bounds for every row. Color names follow the actual packed order west,
north, east, south. The physical-position definition is exactly the
printed941-term floor rank. The main module computes the initializer's
rank504 by complete family sums, including its exceptional first-target
cases. Its south head color is tied to the actual decoded first target1,
whose checked dense state name is93.

The index uniqueness theorem is not tuple uniqueness or physical-rank
bijectivity. These files do not yet prove distinct selector weights, the
sorted physical permutation, tableau/machine semantics, or equivalence of
the Diophantine equation to consistency. Those remain separate obligations.
