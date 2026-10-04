#!/usr/bin/env python3
"""Reproduce tests and example computations using only the standard library."""
from __future__ import annotations

import json
import platform
from pathlib import Path
import subprocess
import sys
from time import monotonic

from unknot import Diagram, Limits, recognize
from unknot.pattern import classify_ball_pattern


def main() -> int:
    root = Path(__file__).resolve().parent
    output = root / 'validation'
    output.mkdir(exist_ok=True)
    start = monotonic()
    process = subprocess.run([sys.executable, '-m', 'unittest', 'discover', '-s', 'tests', '-v'],
                             cwd=root, text=True, capture_output=True, check=False)
    (output / 'unittest.log').write_text(process.stdout + process.stderr, encoding='utf-8')
    print(process.stderr[-250:])
    if process.returncode:
        return process.returncode
    examples = []
    patterns = []
    for filename in sorted((root / 'examples').glob('*.json')):
        value = json.loads(filename.read_text(encoding='utf-8'))
        if filename.name.startswith('pattern_'):
            answer = classify_ball_pattern(value['vertices'], value.get('circles', 0))
            patterns.append({'file': str(filename.relative_to(root)), **answer.to_json()})
            continue
        answer = recognize(Diagram.from_json(value), verify_d2=True)
        if 'expected_rank' in value and answer.reduced_rank != value['expected_rank']:
            raise AssertionError(f"unexpected result in {filename}")
        examples.append({'file': str(filename.relative_to(root)), **answer.to_json()})
    limit_test = recognize(Diagram.from_braid(2, [1, 1, 1]), Limits(max_states=1))
    assert limit_test.status == 'UNKNOWN'
    report = {
        'python': sys.version,
        'platform': platform.platform(),
        'reproducibility': 'deterministic mathematical outputs; timings depend on machine',
        'tests_exit_code': process.returncode,
        'examples': examples,
        'patterns': patterns,
        'resource_limit_example': limit_test.to_json(),
        'elapsed_seconds': monotonic() - start,
        'limitations': [
            'No quasi-polynomial recognition implementation or proof of that bound.',
            'No Lean/formal verification of the Python code.',
            'No independent Regina or KnotTheory executable was run.',
            'External PD fixtures and expected ranks come from the cited Knot Atlas data.',
            'The ball-pattern routine assumes that the manifold is a 3-ball.',
        ],
    }
    (output / 'results.json').write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(f"Recorded {len(examples)} knot cases and {len(patterns)} boundary-pattern cases.")
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
