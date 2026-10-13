"""Whole-source extreme-ray oracle audits of intrinsic common-port queries."""
from itertools import combinations
import random
import sys

from .common import (Block, Prepared, IntrinsicPrepared, source_hashes, save,
                     verify_synchronized, verify_vector, extreme_witness)
from projective_ports.source import synchronized_source
from experiments.oracle import all_rays, positive


def main():
    rng = random.Random(11320261012)
    output = dict(passed=False, models=[], queries=0, positives=0, source_sha256=source_hashes())
    for index in range(180):
        d = 1+index % 3
        blocks = []
        for i in range(2):
            n = 3
            equations = ((1, 1, -1),) if rng.randrange(2) else ()
            ports = tuple(tuple(rng.randrange(3) for _ in range(n)) for _ in range(d))
            conflicts = tuple(pair for pair in combinations(range(n), 2) if rng.random() < .22)
            blocks.append(Block(n, equations, ports, conflicts))
        p = Prepared(blocks)
        q = IntrinsicPrepared(blocks)
        source, _, offsets = synchronized_source(blocks, ((0,)*3,)*2)
        rays = all_rays(source.n, source.equations, source.conflicts)
        record = dict(index=index, blocks=[dict(n=b.n, equations=b.equations, ports=b.ports,
            conflicts=b.conflicts) for b in blocks], dimension=d, intrinsic_dimension=q.reduction.dimension,
            original_stats=p.stats, reduced_stats=q.prepared.stats, queries=[])
        for _ in range(12):
            costs = tuple(tuple(rng.randrange(-4, 5) for _ in range(3)) for _ in blocks)
            master = tuple(rng.randrange(-3, 4) for _ in range(d))
            zeros = tuple(tuple(j for j in range(3) if rng.random() < .2) for _ in blocks)
            _, c, _ = synchronized_source(blocks, costs, master)
            zz = tuple(off+j for off, z in zip(offsets, zeros) for j in z)
            expected = bool(positive(rays, c, zz))
            old = p.solve(costs, master=master, zeros=zeros)
            new = q.solve(costs, master=master, zeros=zeros)
            assert (old['status']=='POSITIVE') == expected == (new['status']=='POSITIVE')
            certificate = None
            if expected:
                assert verify_synchronized(blocks, costs, new, master=master, zeros=zeros)
                x = tuple(v for row in new['vectors'] for v in row)
                certificate = extreme_witness(source, x, c)
                assert verify_vector(source.n, source.equations, source.conflicts, c,
                    certificate['coordinates'], zeros=zz, extreme=True)
                assert certificate['coordinates'] in rays
                output['positives'] += 1
            output['queries'] += 1
            record['queries'].append(dict(costs=costs, master=master, zeros=zeros, expected=expected,
                                          answer=new, certificate=certificate))
        output['models'].append(record)
    output['passed'] = True
    save(sys.argv[1], output)
    print(output['queries'], 'queries;', output['positives'], 'positive source certificates')


if __name__ == '__main__':
    main()
