"""Independent exact fixtures for the new packing lemma.

Run with Python 3.10+; optionally pass an output JSON path.
"""
import json
import sys
from collections import Counter
from fractions import Fraction
from itertools import product
from pathlib import Path
from random import Random

from orbit_packing import (conditional_variance, expected_variance_closed,
                          greedy_labels, labels, orbit_pack, require, scalar)


def main():
    counts = Counter()
    witnesses = []
    pairs = ((0, 0), (0, 1), (1, 0), (1, 1))
    vertices = ((0, 0), (0, 1), (1, 0), (1, 1))
    for multiplicities in product(range(3), repeat=4):
        edges = tuple(edge for edge, n in zip(pairs, multiplicities) for _ in range(n))
        for r, a in ((2, 1), (2, 2), (3, 1)):
            domain = labels(r, a)
            q = len(domain)
            direct_average = Fraction()
            for choice in product(domain, repeat=4):
                assignment = dict(zip(vertices, choice))
                out = orbit_pack(edges, assignment, r, a)
                require(out['variance'] == conditional_variance(edges, assignment, q),
                        "Realized collision formula mismatch")
                direct_average += out['variance']
                counts['exhaustive_labelings'] += 1
            direct_average /= q**4
            require(direct_average == expected_variance_closed(edges, q),
                    "Expected variance differs from exhaustive average")
            require(direct_average == conditional_variance(edges, {}, q),
                    "Empty-assignment conditional expectation mismatch")
            chosen, trace = greedy_labels(edges, r, a)
            out = orbit_pack(edges, chosen, r, a)
            require(out['variance'] <= direct_average, "Greedy construction exceeded mean")
            counts['exhaustive_graph_parameter_pairs'] += 1
            counts['greedy_labelings'] += 1
    rng = Random(20261027)
    for i in range(30):
        nl, nr = rng.randint(1, 4), rng.randint(1, 4)
        edges = tuple((rng.randrange(nl), rng.randrange(nr)) for _ in range(rng.randint(1, 18)))
        r, a = ((2, 3), (3, 2), (4, 1))[i % 3]
        q = r**a
        chosen, trace = greedy_labels(edges, r, a)
        out = orbit_pack(edges, chosen, r, a)
        require(out['variance'] <= expected_variance_closed(edges, q),
                "Random fixture exceeded closed expected variance")
        degree = max(max(Counter(u for u, _ in edges).values()),
                     max(Counter(v for _, v in edges).values()))
        require(out['variance'] <= 2*len(edges)*degree, "Source variance envelope failed")
        counts['greedy_labelings'] += 1
        counts['larger_multigraph_fixtures'] += 1
        if i < 4:
            witnesses.append(scalar({k: v for k, v in out.items() if k != 'placements'}))
    edges = ((0, 0),)*3
    q = 4
    exact = expected_variance_closed(edges, q)
    false_simple_graph_envelope = Fraction(3) + Fraction(2*3*3, q)
    require(exact > false_simple_graph_envelope,
            "Negative control failed to expose the parallel-edge variance issue")
    result = {
        'status': 'passed',
        'scope': 'Exact finite packing, conditional expectation, slot orientation, '
                 'marginals, and multigraph covariance checks; not a SAT solver '
                 'or proof of the complete asymptotic theorem.',
        'counts': dict(counts),
        'negative_control': {
            'case': 'Three parallel edges; q=4 labels per side',
            'exact_expected_variance': str(exact),
            'invalid_simple_graph_envelope': str(false_simple_graph_envelope),
            'detected': True,
        },
        'sample_packing_results': witnesses,
    }
    text = json.dumps(result, indent=2)+'\n'
    if len(sys.argv) > 1:
        Path(sys.argv[1]).write_text(text)
    print(text)


if __name__ == '__main__':
    main()
