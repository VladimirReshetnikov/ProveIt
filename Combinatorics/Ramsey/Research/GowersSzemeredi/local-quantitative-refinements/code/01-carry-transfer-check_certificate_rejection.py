#!/usr/bin/env python3
"""Check that several deliberately corrupted certificate files are rejected.
Only the Python standard library is required.
"""
from copy import deepcopy
import json
from pathlib import Path
from carry_certificates import verify

ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    original = json.loads((ROOT / 'certificates' / 'carry.json').read_text())
    verify(original)
    tests = []

    bad = deepcopy(original)
    bad['dimensions'][-1]['count'] += 1
    tests.append(('incorrect_count', bad))

    bad = deepcopy(original)
    bad['dimensions'][-1]['records'].pop()
    tests.append(('missing_branch', bad))

    bad = deepcopy(original)
    records = bad['dimensions'][-1]['records']
    records.append(deepcopy(records[-1]))
    tests.append(('duplicate_branch', bad))

    bad = deepcopy(original)
    rec = next(x for x in bad['dimensions'][-1]['records'] if x['kind'] == 'dual')
    rec['certificate'][0] = '-1'
    tests.append(('negative_dual_multiplier', bad))

    bad = deepcopy(original)
    bad['dimensions'][-1]['records'][0]['certificate'][-1] = '0'
    tests.append(('zero_primal_slack', bad))

    output = {}
    for name, bad in tests:
        try:
            verify(bad)
        except ValueError as exc:
            output[name] = {'rejected': True, 'reason': str(exc)}
        else:
            raise RuntimeError(f'Corrupted data was accepted: {name}')
    path = ROOT / 'results' / 'verifier_negative_tests.json'
    path.write_text(json.dumps(output, indent=2) + '\n')
    print(json.dumps(output, indent=2))


if __name__ == '__main__':
    main()
