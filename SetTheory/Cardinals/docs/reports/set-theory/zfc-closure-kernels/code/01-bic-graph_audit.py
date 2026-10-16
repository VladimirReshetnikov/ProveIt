"""Exhaustive finite-graph checks of positive reachability and guarded images.

The graphs are NOT finite models of QBC or ZF. The set-existence, schema,
and PA results are proved separately in the article.
"""
from __future__ import annotations
import json
from pathlib import Path


def image_table(rows: list[int]) -> list[int]:
    table = [0] * (1 << len(rows))
    for s in range(1, len(table)):
        low = s & -s
        table[s] = table[s ^ low] | rows[low.bit_length() - 1]
    return table


def positive_closure(seed: int, images: list[int]) -> int:
    c = images[seed]
    while True:
        d = c | images[c]
        if c == d:
            return c
        c = d


def audit(max_n: int = 4) -> dict:
    summaries = []
    for n in range(1, max_n + 1):
        full = (1 << n) - 1
        pairs = 0
        for mask in range(1 << (n*n)):
            rows = [(mask >> (i*n)) & full for i in range(n)]
            images = image_table(rows)
            closed_sets = [d for d in range(1 << n) if images[d] & ~d == 0]
            for seed in range(1 << n):
                c = positive_closure(seed, images)
                # Contains the image of the seed, is closed, and is range-pure.
                assert images[seed] & ~c == 0
                assert images[c] & ~c == 0
                assert c & ~images[full] == 0
                # Least such closed set: positive, not reflexive, reachability.
                for d in closed_sets:
                    if images[seed] & ~d == 0:
                        assert c & ~d == 0
                # Guard all edges by x in seed: closure is precisely the image.
                guarded = image_table([rows[i] if seed & (1 << i) else 0
                                       for i in range(n)])
                assert positive_closure(seed, guarded) == images[seed]
                pairs += 1
        summaries.append({'vertices': n, 'graphs': 1 << (n*n),
                          'graph_seed_pairs': pairs})
    return {'scope': 'Finite graph regression checks, not models or formal proofs.',
            'rows': summaries,
            'graphs_total': sum(r['graphs'] for r in summaries),
            'graph_seed_pairs_total': sum(r['graph_seed_pairs'] for r in summaries),
            'closure': 'all passed', 'range_purity': 'all passed',
            'leastness': 'all passed', 'guarded_exact_image': 'all passed'}


if __name__ == '__main__':
    result = audit()
    path = Path(__file__).resolve().parents[1] / 'results' / 'graph_audit.json'
    path.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
