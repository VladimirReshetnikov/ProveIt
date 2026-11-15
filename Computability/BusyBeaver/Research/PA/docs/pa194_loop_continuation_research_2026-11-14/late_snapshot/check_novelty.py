#!/usr/bin/env python3
"""Replay full-tuple novelty against the initial94 plus16 late graph classes.

This reads frozen tables only; no network, Git checkout, or third-party package
is required. The original four source-preserving constructions and the new
AX11H-loop construction must have no match. The old GAX11 artifact must match
late class L01 and is deliberately treated as an inherited duplicate.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / 'comparison'))
from verify_novelty import canonical


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    assert __debug__ and not sys.flags.optimize, 'Run with assertions enabled.'
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out', type=Path, default=HERE / 'novelty.json')
    args = ap.parse_args()
    initial = json.loads((ROOT / 'comparison/full_census.json').read_text())
    delta = json.loads((HERE / 'delta_classes.json').read_text())
    refs = []
    for item in initial['classes']:
        if item['states'] != 194:
            continue
        path = ROOT / 'comparison/representatives' / (item['graph_hash'] + '.tm')
        assert sha(path) == item['representative']['normalized_sha256']
        n, value = canonical(path)
        assert n == 194 and value is not None
        refs.append(('initial:' + item['table_class'], value))
    assert len(refs) == 94
    for item in delta:
        path = HERE / item['representative_file']
        assert sha(path) == item['representative_sha256']
        n, value = canonical(path)
        assert n == 194 and value is not None
        refs.append((item['id'], value))
    assert len(refs) == 110
    assert len({value for _, value in refs}) == 110
    candidates = json.loads((HERE / 'candidate_manifest.json').read_text())
    results, new_values = [], []
    for item in candidates:
        path = HERE / item['path']
        assert sha(path) == item['sha256']
        if item['release_path_if_present']:
            release_path = ROOT / item['release_path_if_present']
            if release_path.exists():
                assert release_path.read_bytes() == path.read_bytes()
        n, value = canonical(path)
        assert n == 194 and value is not None
        matches = [name for name, reference in refs if value == reference]
        if item['expected_novel']:
            assert not matches, (item['name'], matches)
            new_values.append(value)
        else:
            assert item['name'] == 'PA194GAX11' and matches == ['L01']
        results.append({'name': item['name'], 'working_states': n,
                        'dense_sha256': item['sha256'],
                        'canonical_sha256': hashlib.sha256(repr(value).encode()).hexdigest(),
                        'matches': matches, 'claimed_novel': item['expected_novel']})
    assert len(new_values) == len(set(new_values)) == 5
    receipt = {
        'status': 'PASS',
        'initial_snapshot': '32d0d8b7d93a63ad4106c18cdb29b37927acdad2',
        'latest_snapshot': '603c58ca3bd6bf3222fcfc4e308e6b079f65d573',
        'initial_graphs': 94, 'late_added_graphs': 16, 'total_reference_graphs': 110,
        'all_reference_graphs_broadly_distinct': True,
        'comparison': 'Full canonical tuples, not hash equality',
        'transformations': ['arbitrary working-state renaming', 'any spanning initial root',
                            'global L/R reflection', 'global symbol exchange',
                            'terminal-edge write/move ignored'],
        'new_graphs_pairwise_distinct': True, 'new_graph_count': 5,
        'results': results,
        'scope': 'Structural novelty only; no consistency or proof-calibration theorem follows from this comparison.',
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
