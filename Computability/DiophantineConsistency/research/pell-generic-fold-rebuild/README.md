# Generic Pell fold/recovery rebuild

This is a fresh three-module Lean source build of the already-developed
all-index Pell folding and odd-ordinate recovery, for use without importing
the 80-row graph. `PellFold.lean` changes exactly the first line of historical
`/tmp/pell-all-index-fold-ad1a76zq/PellFold.lean` (SHA-256
`d1c55d280615310987f55d68717a671e9ce3cd917bd83697da25129d05388d34`):
it imports `DiophantineConsistency.ArithmeticPellHalfIndex` in place of
`Direct80Joined`. The remaining source bytes are identical. The
`PellOddFold.lean` and `PellRecovery.lean` source copies are unchanged from
the prior checked producers. Thus the generic proofs now build from the named
arithmetic provider without the explicit 80-graph module import.

`run.py` compiled the three modules sequentially, with 8-GiB/two-Lean-process
resource guards, selected direct provider and source pins, snapshots and
strict diagnostics. Accepted `observations/attempt01/` finished with status
PASS and outer command exit 0. The fresh output root is
`/tmp/pell-generic-fold-1n_2g52k`, with object hashes:

* `PellFold.olean`:
  `5a45b94a6ff3dea0ba802c852b84f83daa99aace8415ede0bf682a11100a908b`;
* `PellOddFold.olean`:
  `853721216a20dbf04c1babafbbb79526d92db0aee5f3a6127625d86208bc3175`;
* `PellRecovery.olean`:
  `0deec819d3d49c3ebfe8179175613095e6497272cfc6cc1d7723c8df6b32524a`.

The two later object hashes happen to match the old builds; their imported
module names are resolved from this fresh output root in clients. The theorem
`PellRecovery.recover_odd_ordinate` is a generic conditional model theorem,
not by itself trace75 soundness, a halt bridge or an iPRA theorem. The
selected arithmetic object's package and project transitive ancestry and
dynamic dependencies remain inherited; no complete selected closure scan or
independent replay is claimed.
