# Spatial cycle and canonical cell coordinate

Date: 2026-10-26. Independent complete source/check review and fresh replay:
ROOT. See the [author receipt](current-cell-cycle2011-author.md).

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| CurrentCellCycle2011.lean (171 lines) | 874a68dc11255170f19dc1a5345e195f36379711f8af630b16dd6eb9fe77081d |
| CurrentCellCycle2011Checks.lean (73 lines) | 57f9344d572c115acdf5006d57c6d8874ed66c0b874c12bfe34966192585f6cb |

Both complete frozen files were read before fresh direct root runs with
`lake env lean -M6000 -j1`. Main output was written to a separate temporary
object; checks imported the frozen author-built main object. Both passed.
The main log is empty; all sixteen axiom audits are standard-only. No
whole-closure or umbrella rebuild is claimed.

The spatial successor and predecessor are inverse equivalences of the
exact aligned subtype in ZMod(N*2011), with full coordinates b+2011 and
b-2011. The index b.val/2011 is belowN and reconstructs b.val exactly.
Successor iteration has value b+j*2011 for arbitraryj. Thus every target
is reachable from zero, or any other base, in fewer thanN steps and the
N-th iterate returns to its initial base.

The generic propagation theorem applies to any predicate true at the
initial cell and preserved by successor. It supplies no word, tile or
occupation premise. The actual quotient index also defines the canonical
equivalences with FinN and ZModN, rather than an arbitrary finite bijection.
Concrete singleton checks retain N=1 and show successor/predecessor are
the identity. Native decoding and occupation are subsequent applications.
The displayed decimal equation and its metrics are unchanged.
