#!/usr/bin/env python3
"""Compare named axiom reports in completed focused baseline/candidate checks."""
from pathlib import Path
import argparse
import hashlib
import json
import re


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def profiles(path):
    found = {}
    pattern = r"'([^']+)'\s+(does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])"
    for match in re.finditer(pattern, path.read_text()):
        name, kind, names = match.groups()
        assert name not in found, f'Duplicate axiom report: {name}'
        found[name] = [] if names is None else sorted(name.strip() for name in names.split(','))
    assert found, f'No named axiom reports in {path}'
    return found


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--results', type=Path,
                        default=Path(__file__).resolve().parent / 'verification')
    parser.add_argument('--out', type=Path)
    args = parser.parse_args()
    root = args.results.resolve()
    result = json.loads((root / 'result.json').read_text())
    assert result['status'] == 'PASS'
    for lane in ('baseline', 'candidate'):
        run = result['runs'][lane]
        assert run['status'] == 'PASS'
        assert len(run['records']) == run['total_compilations']
        objects = {}
        for row in run['records']:
            assert row['exit_code'] == 0 and not row['sorry_warning'], row['module']
            assert sha(root / row['log']) == row['log_sha256'], row['module']
            for name, digest in row['direct_import_objects'].items():
                assert objects[name] == digest, (row['module'], name)
            objects[row['module']] = row['object_sha256']
    comparisons = {}
    for client, expected_count in [('BasisPublicAudit', 4), ('DownstreamPublicAudit', 6)]:
        baseline = profiles(root / 'baseline/logs' / (client + '.log'))
        candidate = profiles(root / 'candidate/logs' / (client + '.log'))
        assert len(baseline) == expected_count and baseline == candidate, client
        comparisons[client] = {'identical_named_profiles': True, 'profiles': candidate}
    generic = profiles(root / 'candidate/logs/BusyBeaver.ZFC.DominatedImplication.log')
    unrestricted = profiles(root / 'candidate/logs/BusyBeaver.ZFC.ImplicationalBasis.log')
    assert len(generic) == 6 and all(not value for value in generic.values())
    assert len(unrestricted) == 4 and all(not value for value in unrestricted.values())
    comparison = {
        'status': 'PASS',
        'scope': 'Focused component axiom profiles; not a full endpoint check.',
        'result_sha256': sha(root / 'result.json'),
        'client_comparisons': comparisons,
        'generic_core_profiles': generic,
        'unrestricted_adapter_profiles': unrestricted,
        'all_compiler_log_digests_match': True,
        'recorded_import_objects_match_the_recorded_fresh_provider_objects': True,
    }
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(comparison, indent=2) + '\n')
    print('PASS: 10 named baseline/candidate profiles agree; 6 generic and 4 adapter exports are axiom-free.')


if __name__ == '__main__':
    main()
