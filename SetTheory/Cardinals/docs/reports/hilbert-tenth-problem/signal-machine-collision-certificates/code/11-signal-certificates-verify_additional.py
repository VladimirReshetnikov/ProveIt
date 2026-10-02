"""Independent exact-arithmetic edge and height checks for the sparse compiler."""
from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import json, random
from signal_geometry import trace, polynomial, linear_rank
from signal_sparse import compile_sparse, sparse_witness

rng = random.Random(73102026)
speeds = {'a': 0, 'b': 2, 'c': 3, 'd': 4}
subsets = [x for k in range(2, 5) for x in combinations(speeds, k)]
fixtures = [
    ((speeds, {}), [], [], 0),
    ((speeds, {}), ['a'], [0], 0),
    ((speeds, {}), ['d'], [0], 0),
    ((speeds, {}), list('abcd'), [0, 1, 2, 3], 0),
    ((speeds, {frozenset('ad'): ()}), list('dada'), [0, 4, 8, 12], 10),
    ((speeds, {frozenset('ad'): tuple('abcd')}), list('dada'), [0, 4, 8, 12], 10),
]
for _ in range(500):
    rules = {frozenset(x): tuple(rng.sample(list(speeds), rng.randrange(5))) for x in subsets}
    n = rng.randrange(11)
    labels = [rng.choice(list(speeds)) for _ in range(n)]
    positions = []
    p = 0
    for i in range(n):
        p += (rng.randrange(11) if i == 0 else rng.randrange(1, 11))
        positions.append(p)
    fixtures.append(((speeds, rules), labels, positions, 10))

counts = dict(fixtures=len(fixtures), certificates=0, terminal_certificates=0,
              exact_height_checks=0, local_growth_checks=0, exact_rank_checks=0)
for machine, labels, positions, cap in fixtures:
    layers = trace(machine, labels, positions, cap)
    M0 = max(positions, default=0)
    Mprev = M0
    elapsed = F(0)
    for j, layer in enumerate(layers, 1):
        assert layer['dt'] <= Mprev
        elapsed += layer['dt']
        assert elapsed <= F(M0 * (5**j - 1), 4)
        assert max(layer['end'], default=F(0)) <= 5**j * M0
        Mprev = max(layer['positions'], default=F(0))
        counts['local_growth_checks'] += 1
    final_labels = layers[-1]['labels'] if layers else labels
    halted = all(speeds[a] <= speeds[b] for a,b in zip(final_labels, final_labels[1:]))
    for halt in [False] + ([True] if halted else []):
        cert = compile_sparse(machine, labels, [x['blocks'] for x in layers], halt=halt)
        assignment = sparse_witness(cert, positions, layers)
        assert polynomial(cert, assignment) == 0
        assert max(assignment.values(), default=0) <= 60**len(layers) * max(1, M0)
        assert cert['counts']['lifetimes'] <= max(len(labels)-1, 0) + sum(len(x['outgoing'])+1 for x in cert['events'])
        counts['certificates'] += 1
        counts['terminal_certificates'] += int(halt)
        counts['exact_height_checks'] += 1
        if cert['variables'] and counts['exact_rank_checks'] < 12:
            assert linear_rank(cert) == len(cert['variables'])
            counts['exact_rank_checks'] += 1
Path(__file__).with_name('additional_verification_receipt.json').write_text(json.dumps(counts, indent=2)+'\n')
print(json.dumps(counts, indent=2))
