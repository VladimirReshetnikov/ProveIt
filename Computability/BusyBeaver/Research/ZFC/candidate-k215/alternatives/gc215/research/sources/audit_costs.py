#!/usr/bin/env python3
"""Recompute the delivered research source costs; no optimizer or TM proof.

Run from any directory. Paths in the companion ledger are archive-root relative.
Historical optimization receipts are checked only for exact file identity.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('Assertions must be enabled; do not use -O.')
ROOT = Path(__file__).resolve().parents[2]
LEDGER = ROOT / 'research/research_costs.json'


def metrics(rows):
    assert isinstance(rows, list) and rows
    by_path = {}
    for path, op, arg in rows:
        assert isinstance(path, str) and set(path) <= {'0', '1'}
        assert path not in by_path
        assert op in ('CI', 'CD', 'CB', 'CC', 'CH')
        if op in ('CI', 'CD'):
            assert isinstance(arg, int) and 0 <= arg <= 8
        elif op in ('CB', 'CC'):
            assert isinstance(arg, int) and arg >= 1
        else:
            assert arg is None
        by_path[path] = (op, arg)
    maximum = max(map(len, by_path))
    nodes, ordered = set(), []

    def parse(path=''):
        if path in by_path:
            node = by_path[path]
            ordered.append([path, *node])
        else:
            assert len(path) < maximum, ('Missing leaf', path)
            node = (parse(path + '0'), parse(path + '1'))
        nodes.add(node)
        return node

    parse()
    assert ordered == rows, 'Rows must be the complete ordered prefix tree'
    return {'dag_nodes': len(nodes), 'leaf_occurrences': len(rows),
            'maximum_depth': maximum,
            'maximum_zero_run': max(len(run) for path in by_path
                                    for run in path.split('1'))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    ledger = json.loads(LEDGER.read_text())
    records = {}

    def walk(value):
        if isinstance(value, dict):
            if 'file' in value and 'sha256' in value:
                name = value['file']
                if name in records:
                    assert records[name]['sha256'] == value['sha256']
                records[name] = value
            for child in value.values():
                walk(child)
        elif isinstance(value, list):
            for child in value:
                walk(child)

    walk(ledger)
    source_results = []
    for name, entry in sorted(records.items()):
        path = (ROOT / name).resolve()
        assert ROOT in path.parents and path.is_file(), name
        raw = path.read_bytes()
        assert hashlib.sha256(raw).hexdigest() == entry['sha256'], name
        if 'metrics' in entry:
            got = metrics(json.loads(raw))
            assert got == entry['metrics'], (name, got, entry['metrics'])
            source_results.append({'file': name, **got})
    result = {'status': 'SOURCE_COST_AND_RECEIPT_HASH_AUDIT_PASS',
              'files_checked': len(records),
              'distinct_source_files': len(source_results),
              'experiments': len(ledger['experiments']),
              'sources': source_results,
              'scope': 'Exact literal source costs and archived receipt hashes only. No source semantic claim, optimizer replay, or binary-runtime verification.'}
    text = json.dumps(result, indent=2) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
