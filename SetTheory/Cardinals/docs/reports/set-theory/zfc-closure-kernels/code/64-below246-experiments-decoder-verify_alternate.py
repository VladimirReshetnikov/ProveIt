#!/usr/bin/env python3
"""Replay all universal instruction cases and the exact alternate bootstrap.

Uses the inherited ordinary symbolic-induction interface. This does not
invoke a proof-assistant kernel or assert a state-count improvement.
"""
from pathlib import Path
import hashlib
import json
import os

HERE = Path(__file__).resolve().parent
os.environ['ZFC246_TABLE'] = str(HERE / 'detector8-context246.tm')
import fold_search246 as f


def main():
    if not __debug__:
        raise SystemExit('Assertions must be enabled.')
    digest = hashlib.sha256(f.TABLE.read_bytes()).hexdigest()
    assert digest == '2e4c60cf14947c9ebb8e4bf999f9cd0ac995d09d16bb8b84e5c2fba922f79b1b'
    assert len(f.T) == 492
    for i in range(len(f.CASES)):
        ok, _, reason = f.check(f.T, i, 1000)
        assert ok, (i, f.CASES[i][:4], reason)
    actual = f.bootstrap(f.T, 500000)
    expected = json.loads((HERE / 'detector8-bootstrap.json').read_text())
    assert actual['outcome'] == 'complete_safe_root_candidate'
    for key in ['steps', 'head', 'header', 'values', 'spares', 'ones']:
        assert actual[key] == expected[key], key
    assert actual['steps'] == 409449
    assert actual['values'] == [0, 0, 0, 3, 0, 0, 3, 0, 0]
    assert actual['spares'] == [1]*167
    logical = [actual['values'][f.L.PHYSICAL[r]] for r in range(9)]
    assert logical == [3, 0, 0, 0, 3, 0, 0, 0, 0]
    print(json.dumps({'status': 'PASS', 'working_states': 246,
        'instruction_cases': len(f.CASES), 'bootstrap_steps': actual['steps'],
        'complete_tape_matches_recorded_bootstrap': True,
        'logical_values': logical, 'table_sha256': digest,
        'proof_status': 'Ordinary symbolic and finite checks; no new kernel endpoint.'}, indent=2))


if __name__ == '__main__':
    main()
