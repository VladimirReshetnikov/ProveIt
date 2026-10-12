"""Replay the bounded dispatcher on all supplied native and relabelled inputs."""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import sys
from unittest.mock import patch


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    sys.path.insert(0, str(args.root))
    from activation_forests import from_dense
    from integration.bounded_prefix import solve_prefix
    from integration.verify_prefix import verify_prefix
    sources = json.loads((args.root/'results/native_study.json').read_text())
    relabels = json.loads((args.root/'results/relabel_study.json').read_text())
    records = []
    for case in sources['cases']:
        for kind in ('source', 'finite_boundary'):
            p = case[kind]['problem']
            r = solve_prefix(p)
            assert verify_prefix(p, r)
            assert r['status'] == case[kind]['stopping_result']['status']
            records.append({'id': case['id'], 'matrix': kind, 'result': r})
    for case in relabels['cases']:
        p = case['problem']
        r = solve_prefix(p)
        assert verify_prefix(p, r)
        assert (r['status'] == 'SUCCESS') == case['oracle']['exists']
        records.append({'id': 'relabel/'+str(case['trial']), 'matrix': 'finite_boundary', 'result': r})
    # The stress corpus happens to finish in the incumbent. Exercise the
    # fallback and its independent certificate dispatch explicitly as well.
    controls = []
    for p in [from_dense(3, [[0,1],[1,2],[2,0]], [[1],[1],[1]]),
              from_dense(2, [[0,1]]*3, [[1],[1],[1]])]:
        with patch('integration.bounded_prefix.solve_by_stopping',
                   return_value={'status': 'INCONCLUSIVE'}):
            r = solve_prefix(p)
        assert r['stats']['backend'] == 'output'
        assert verify_prefix(p, r)
        controls.append({'problem':p,'result':r})
    huge = from_dense(1 << 16384, [[0, 1]], [[]])
    r = solve_prefix(huge)
    assert r['stats']['backend'] == 'output' and verify_prefix(huge,r)
    controls.append({'description': '16384-bit disconnected namespace; sparse output route',
                     'verified': True})
    bad = json.loads(json.dumps(records[0]['result']))
    bad['certificate']['input_sha256'] = '0'*64
    assert not verify_prefix(sources['cases'][0]['source']['problem'], bad)
    payload = {'scope': 'Optional polynomial-prefix dispatcher; geometry is supplied separately.',
        'cases': records, 'controls': controls, 'verified_cases': len(records),
        'statuses': dict(Counter(r['result']['status'] for r in records)),
        'backends': dict(Counter(r['result']['stats']['backend'] for r in records)),
        'maximum_incumbent_search_nodes': max(r['result']['stats']['backend_stats'].get(
            'search_nodes',0) for r in records),
        'code_sha256': {p.name:sha256(p.read_bytes()).hexdigest()
                       for p in (args.root/'integration').glob('*.py')}}
    out = args.output or args.root/'results/prefix_results.json'
    out.write_text(json.dumps(payload,indent=2)+'\n')
    print(json.dumps({k:payload[k] for k in ['verified_cases','statuses','backends',
                                           'maximum_incumbent_search_nodes']}))


if __name__ == '__main__':
    main()
