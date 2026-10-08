#!/usr/bin/env python3
"""Verify package integrity and the source hashes recorded by both research runs.

This checks file identity, not the mathematical conclusions or performance.
Run from any working directory, before regenerating included artifacts.
"""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
SUBTREE = ROOT / 'reproducibility/ProveIt/Topology/UnknotRecognition'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    failures, count = [], 0
    for line in (ROOT / 'MANIFEST.sha256').read_text().splitlines():
        expected, name = line.split('  ', 1)
        path = ROOT / name
        if not path.is_file() or digest(path) != expected:
            failures.append(name)
        count += 1
    records = {}
    for name, key in (('modular_benchmarks.json', 'sources_after'),
                      ('modular_audit.json', 'sources')):
        result = json.loads((SUBTREE / 'fast/results' / name).read_text())
        for path, expected in result[key].items():
            source = SUBTREE / path
            if not source.is_file() or digest(source) != expected:
                failures.append(name + ': ' + path)
        records[name] = len(result[key])
    print(json.dumps({'manifest_files': count, 'recorded_source_files': records,
                      'failures': failures, 'status': 'passed' if not failures else 'failed'}, indent=2))
    if failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
