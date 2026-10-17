"""One sigma-partition lemma.

`Proofs05Lemma14.section5_sigma_partition` (private) and
`Proofs05Lemma9Induction.section5Nat_sigma_partition` were the same statement about `IsPartition`
over any type: refining every cell of a partition by a partition gives a partition indexed by the
sigma type. It moves to `ProofInfrastructure`, next to `IsPartition.cell_subset`, as
`IsPartition.sigma`.
"""
import re

from foldlib import Fold

F = Fold()
blk = F.take('Proofs05Lemma9Induction', 'section5Nat_sigma_partition')
F.delete_decl('Proofs05Lemma14', 'section5_sigma_partition')
assert blk.startswith('theorem section5Nat_sigma_partition'), blk[:60]
blk = blk.replace('theorem section5Nat_sigma_partition',
                  '/-- Refining every cell of a partition by a partition gives a partition\n'
                  'indexed by the sigma type. -/\ntheorem IsPartition.sigma', 1)
F.insert('ProofInfrastructure', blk, 'IsPartition.sum_card')
for m, a in [('Proofs05Lemma14', 'section5_sigma_partition'),
             ('Proofs05Lemma9Induction', 'section5Nat_sigma_partition'),
             ('Proofs05BoxTransport', 'section5Nat_sigma_partition')]:
    s = F.get(m)
    assert re.search(r"(?<![\w'])" + a + r"(?![\w'])", s), (m, a)
    F.text[m] = re.sub(r"(?<![\w'])" + a + r"(?![\w'])", 'IsPartition.sigma', s)
F.commit()
