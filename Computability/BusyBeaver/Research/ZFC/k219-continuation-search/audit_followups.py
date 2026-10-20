#!/usr/bin/env python3
"""Read-only metadata/census audit; does not import or execute search programs."""
from pathlib import Path
import argparse
import collections
import gzip
import hashlib
import itertools
import json
import re

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def table(path):
    rows = {}
    start = None
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):
            start = int(line.split()[-1])
        elif line and not line.startswith('#'):
            q, b, w, d, z = line.split()
            row = int(q), int(b)
            assert row not in rows and d in ('L', 'R')
            rows[row] = int(w), -1 if d == 'L' else 1, int(z)
    assert start is not None and len(rows) % 2 == 0
    return rows, start


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    descriptors = json.loads((ROOT / 'inputs.json').read_text())
    tables = {d['name']: table((ROOT / d['path']).resolve()) for d in descriptors['seeds']}
    reports = []
    families = [
        ('engine-helpers-run1', 'search_engine_helpers.py', 'search.py', 19064),
        ('66-198-run1', 'search_66_198.py', 'search_66_198.py', 95922),
        ('hidden198-run1', 'search_hidden198.py', 'search_hidden198.py', 1752),
        ('hidden-states-run1', 'search_hidden_states.py', 'search_hidden_states.py', 190092),
    ]
    for name, source, snapshot, expected in families:
        directory = ROOT / 'results' / name
        record = json.loads((directory / 'result.json').read_text())
        source_hash = record.get('source_sha256', record.get('search_sha256'))
        assert sha(ROOT / source) == sha(directory / snapshot) == source_hash
        for path, digest in record['inputs'].items():
            assert sha(Path(path)) == digest
        assert record['attempted'] == expected and record['hits'] == []
        assert record['status'].startswith('COMPLETE')
        assert record.get('radius', record.get('filter_radius')) == 7
        assert record.get('fuel', record.get('filter_fuel')) == 97
        digest = record.get('rejection_stream_sha256', record.get('rejections_sha256'))
        assert sha(directory / 'rejections.jsonl.gz') == digest
        by_seed = collections.Counter()
        reasons = collections.Counter()
        specifications = collections.defaultdict(set)
        with gzip.open(directory / 'rejections.jsonl.gz', 'rt') as stream:
            for index, line in enumerate(stream, 1):
                rejection = json.loads(line)
                assert rejection['id'] == index
                seed = rejection['seed']
                old, start = tables[seed]
                states = {q for q, b in old}
                failure = rejection.get('failure', rejection.get('witness'))
                assert failure['radius'] == 7 and failure['fuel'] == 97
                assert 0 <= failure['window'] < 2 ** 15
                by_seed[seed] += 1
                reasons[failure['reason']] += 1
                if name.startswith('hidden'):
                    hidden = rejection.get('hidden', 198)
                    entry = tuple(rejection.get('entry', [66, 0]))
                    assert hidden != start and entry[0] != hidden
                    assert [row for row, action in old.items() if action[2] == hidden] == [entry]
                    action = tuple(rejection['action'])
                    assert action[0] in (0, 1) and action[1] in (-1, 1)
                    assert action[2] in (states - {hidden}) | {254}
                    key, spec = (seed, hidden), action
                else:
                    keep, drop = rejection['keep'], rejection['drop']
                    assert keep in states and drop in states and keep != drop
                    assert start not in (keep, drop)
                    if name == 'engine-helpers-run1':
                        assert {keep, drop} & {198, 113, 66, 40, 54}
                    else:
                        assert (keep, drop) == (66, 198)
                        assert all(row[:2] == [1, -1] for row in rejection['rows'])
                    key, spec = (seed, keep, drop), tuple(map(tuple, rejection['rows']))
                assert spec not in specifications[key]
                specifications[key].add(spec)
        assert index == expected == sum(by_seed.values())
        if name.startswith('hidden'):
            for (seed, hidden), actions in specifications.items():
                states = {q for q, b in tables[seed][0]}
                assert actions == set(itertools.product((0, 1), (-1, 1), sorted((states - {hidden}) | {254})))
        if name == 'hidden-states-run1':
            assert record['completed'] == record['candidate_count'] == expected
            for seed in record['seeds']:
                old, start = tables[seed['seed']]
                incoming = collections.defaultdict(list)
                for row, action in old.items():
                    incoming[action[2]].append(row)
                eligible = {q for q, b in old if q != start and len(incoming[q]) == 1 and incoming[q][0][0] != q}
                assert {s['hidden'] for s in seed['states']} == eligible
                assert len(eligible) == seed['eligible_count']
                assert len(eligible) + len(seed['excluded']) == 219
                for s in seed['states']:
                    assert s['status'] == 'COMPLETE' and s['entry_contexts'] > 0
                    assert s['attempted'] == s['completed'] == s['rejected'] == 876
                    assert s['survivors'] == 0
                    assert len(specifications[seed['seed'], s['hidden']]) == 876
            controls = json.loads((directory / 'controls.json').read_text())
            assert controls['status'] == 'TWO_SYNTHETIC_CONTROLS_PASS'
        reports.append({'run': name, 'result_sha256': sha(directory / 'result.json'),
                        'source_sha256': source_hash, 'rejections': expected,
                        'by_seed': dict(by_seed), 'reasons': dict(reasons),
                        'seconds': record['seconds']})
    selective = []
    for n, count, source in [(1, 229, 'selective_protection.py'), (2, 222, 'selective_protection_v2.py')]:
        directory = ROOT / 'results' / f'selective-run{n}'
        record = json.loads((directory / 'result.json').read_text())
        assert (ROOT / source).read_bytes() == (directory / 'selective_protection.py').read_bytes()
        assert record['status'] == 'BOUNDED_SELECTIVE_ALLOCATION_MEASUREMENT_COMPLETE'
        assert record['baseline_identity']['working_states'] == 219
        for path, digest in record['inputs'].items():
            assert sha(Path(path)) == digest
        for variant in record['variants']:
            d = directory / variant['name']
            assert sha(d / 'sites.json') == variant['source_sha256']
            assert variant['attempts'] == 2 and variant['status'] == 'DECODER_PREFIX_BINDING_PASS'
            raw = d / 'raw-binding-valid.native.tm'
            assert sha(raw) == variant['final_attempt']['raw_sha256']
            rows, _ = table(raw)
            assert len(rows) == 2 * count
            assert variant['final_attempt']['metrics']['working_states'] == count
            assert (d / 'attempt-00.json').exists() and (d / 'rejected-00.native.tm').exists()
        selective.append({'run': n, 'result_sha256': sha(directory / 'result.json'), 'states': count})
    links = re.findall(r'\]\(([^)]+)\)', (ROOT / 'README.md').read_text())
    local = [x.split('#')[0] for x in links if not x.startswith(('https:', 'http:', '#'))]
    assert all((ROOT / x).exists() for x in local)
    output = {'status': 'FOLLOWUP_METADATA_CENSUS_PASS', 'reviewer': 'drop_contract',
              'role': 'Search/allocator author; metadata and literal table census only. No search rerun, independent proof verification or candidate runtime claim.',
              'audit_source_sha256': sha(Path(__file__)), 'search_runs': reports,
              'selective_runs': selective, 'readme_sha256': sha(ROOT / 'README.md'),
              'local_links_checked': len(local),
              'scope': 'Exact source snapshots, current input pins, all rejection stream IDs/actions/censuses, strict incoming eligibility, raw allocator row counts, and retained failure paths. Failed diagram semantics were not replayed.'}
    args.output.write_text(json.dumps(output, indent=2) + '\n')
    print(json.dumps({'status': output['status'], 'rejections': sum(r['rejections'] for r in reports), 'local_links_checked': len(local)}))


if __name__ == '__main__':
    main()
