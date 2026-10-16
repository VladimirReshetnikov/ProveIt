"""Same expanded-tree metric as source 02, with new pure-bound controls."""
from __future__ import annotations
import json
from pathlib import Path
from kernel import *


def main() -> dict:
    data = {'metric': 'Occurrence tree in {membership,equality,bottom,implication,forall}; holes count once per occurrence. No variable payload, arbitrary parameter closure, proof-engine or TM costs.',
            'prior_basis_blob': 'a49a01793a23d41c92da7a1953adb70f0772d8e3',
            'theories': {}}
    for prefix, ax, seed in [('T_point', extensionality(), 'point'),
                              ('T_subset', extensionality(), 'subset'),
                              ('Q_subset', congruence(), 'subset')]:
        for mixed in [True, False]:
            for curried in [False, True]:
                f = closure(Hole(0, 1), seed, mixed, False, curried)
                terms = [ax, f]
                co: dict[str, int] = {}
                for g in terms:
                    for k, n in counts(g).items(): co[k] = co.get(k, 0) + n
                name = prefix + ('_mixed' if mixed else '_pure') + ('_curried' if curried else '')
                data['theories'][name] = {'nodes': sum(co.values()), 'constructors': co}
    expected = {'T_point_mixed':69, 'T_subset_mixed':72, 'Q_subset_mixed':83,
                'T_point_pure':65, 'T_subset_pure':68, 'Q_subset_pure':79}
    for k, n in expected.items():
        if data['theories'][k]['nodes'] != n: raise AssertionError((k, data['theories'][k]))
    dest = Path(__file__).resolve().parents[1] / 'results' / 'metrics.json'
    dest.write_text(json.dumps(data, indent=2) + '\n')
    print(json.dumps({k:v['nodes'] for k,v in data['theories'].items()}, indent=2))
    return data

if __name__ == '__main__': main()
