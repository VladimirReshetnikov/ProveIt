# Generic Pell rank reduction rebuild

The generic `PellRankReduction.rank_to_main_index` source was rebuilt without
its historical 80-specific `SignedRankIndex` import. Compared with the retained
historical source `/tmp/pell-rank-reduction-2v7bmiw4/PellRankReduction.lean`
(SHA-256 `8ebe1aa951f7a6c21709c6086b59fba29a9c4511e7fb008070baade612047e8d`),
the only source change replaces that first import with
`DiophantineConsistency.ArithmeticPellResidueAux`; the proof body is identical.
The generic theorem transfers explicit signed residues and divisibility from a
strong Pell index to a supplied main index. It does not bind any graph, prove
an index equality, or establish halting/iPRA.

`run.py` accepted `observations/attempt01/`, compiling the source into fresh
`/tmp/pell-rank-generic-_nzvtqaf/PellRankReduction.olean` with SHA-256
`1cb551f5865a5c7a2ba6cdf762415181cef24a01dc5666a1ca9d5bd529f27325`.
The source SHA-256 is
`fa624649df7e97d02e08f069cde8c99c36fd0a6e1d0191629fa6498c8268bdc5`.
Selected direct provider bytes and resources are recorded and pinned;
project/package transitive, historical source/object and dynamic ancestry
remain inherited. This is not a full closure audit or independent replay.
