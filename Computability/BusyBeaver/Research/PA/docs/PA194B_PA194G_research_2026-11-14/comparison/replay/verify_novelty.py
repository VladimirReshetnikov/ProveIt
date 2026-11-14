#!/usr/bin/env python3
"""Fast, exact structural distinction by an isomorphism invariant.

The frozen prior corpus has 82 complete 194-state tables, each with 21
self-loop edges. The delivered PA194B has 22. This invariant is preserved
by state renaming, root choice, reflection, symbol exchange, and arbitrary
terminal write/move actions. It certifies nonidentity, not correctness.
"""
from pathlib import Path
import argparse
import collections
import hashlib
import json
from literal_inventory import parse_table, canonical

HERE = Path(__file__).resolve().parent


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--candidate', type=Path, required=True)
    ap.add_argument('--frontier', type=Path, default=HERE / 'frontier_tables')
    ap.add_argument('--manifest', type=Path, default=HERE / 'table_manifest.json')
    ap.add_argument('--output', type=Path, default=Path.cwd() / 'novelty-replay.json')
    args = ap.parse_args()
    manifest = json.loads(args.manifest.read_text())
    prior = []
    for item in manifest['tables']:
        raw = (args.frontier / item['file']).read_bytes()
        assert hashlib.sha256(raw).hexdigest() == item['sha256'], item['file']
        data = parse_table(raw)
        assert data is not None, item['file']
        rows, states, halt = data
        if len(states) != 194:
            continue
        # At least one spanning root distinguishes complete tables from fragments.
        assert any(canonical(data, q) is not None for q in sorted(states))
        loops = sum(target == q for (q, bit), (write, move, target) in rows.items())
        prior.append(dict(file=item['file'], self_loop_edges=loops))
    raw = args.candidate.read_bytes()
    data = parse_table(raw)
    assert data is not None
    rows, states, halt = data
    assert len(states) == 194 and len(rows) == 388
    assert canonical(data, 0) is not None, 'Dense candidate must span from start zero'
    loops = sum(target == q for (q, bit), (write, move, target) in rows.items())
    distribution = dict(sorted(collections.Counter(x['self_loop_edges'] for x in prior).items()))
    assert len(prior) == 82 and distribution == {21: 82}
    assert loops == 22
    result = dict(status='PASS', snapshot=manifest['snapshot'],
                  candidate=args.candidate.name,
                  candidate_sha256=hashlib.sha256(raw).hexdigest(),
                  prior_classes=len(prior), prior_self_loop_distribution=distribution,
                  candidate_self_loop_edges=loops,
                  reasoning='Self-loop edge count is invariant under every stated cosmetic transformation.',
                  scope='Literal table nonidentity only; not a consistency or runtime-correctness proof.',
                  prior=prior)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'prior'}, indent=2))


if __name__ == '__main__':
    main()
