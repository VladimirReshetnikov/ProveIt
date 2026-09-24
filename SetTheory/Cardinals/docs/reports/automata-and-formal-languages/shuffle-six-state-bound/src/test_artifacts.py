#!/usr/bin/env python3
"""Check redundant encodings and that the C++ verifier rejects bad/missing data."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('verifier', type=Path)
    args = parser.parse_args()
    binary = args.verifier.resolve()
    lines = (ROOT/'data/certificates.txt').read_text().splitlines()
    records = [json.loads(line) for line in (ROOT/'data/certificates_masks.jsonl').read_text().splitlines()]
    data_lines = [line for line in lines if line and not line.startswith('#')]
    require(len(data_lines) == len(records), 'encoding record counts differ')
    for d, line in zip(records, data_lines):
        expected = [d['m'], d['n'], d['key']] + d['f'] + d['g'] + d['predecessor']
        require(list(map(int, line.split())) == expected, 'text and JSON disagree')
    print(f'PASS: JSON and text encodings agree for {len(records)} records.')
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        # A valid-domain but semantically wrong transformation in the 3-row record.
        changed = list(map(int, data_lines[0].split()))
        changed[3] = (changed[3] + 1) % changed[0]
        cases = {
            'modified-map': [' '.join(map(str, changed))] + data_lines[1:],
            'missing-three-row-certificate': data_lines[1:],
        }
        for label, rows in cases.items():
            path = tmp/(label+'.txt')
            path.write_text('\n'.join(rows)+'\n')
            run = subprocess.run([str(binary), str(path)], text=True, capture_output=True)
            require(run.returncode != 0, f'verifier accepted {label}')
            require('FAIL:' in run.stderr, 'missing rejection explanation')
            print(f'PASS: rejected {label}: {run.stderr.strip()}')


if __name__ == '__main__':
    main()
