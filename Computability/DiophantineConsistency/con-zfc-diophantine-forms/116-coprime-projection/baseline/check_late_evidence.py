#!/usr/bin/env python3
"""Authenticate selected comparator sources and count their literal live gates.
No upstream programs are imported or executed. Degree values remain reported
source claims, not independently re-proved by this metadata/count audit.
"""
from pathlib import Path, PurePosixPath
import copy
import hashlib
import json

HERE = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def count_graph(packet):
    leaves = packet['witnesses'] + packet['fixed_numerals']
    require(len(leaves) == len(set(leaves)), 'Duplicate declared leaf')
    known = set(leaves)
    rows = {}
    for row in packet['source']:
        require(isinstance(row, list) and len(row) == 4, 'Invalid arithmetic row')
        name, operation, a, b = row
        require(name not in known and operation in ('+', '-', '*'), 'Invalid gate or operation')
        require(all((isinstance(v, str) and v in known) or type(v) is int
                    for v in (a, b)), 'Noncausal or nonliteral operand')
        rows[name] = row
        known.add(name)
    require(packet['output'] in rows, 'Missing output')
    live = set()
    def visit(name):
        if name in live:
            return
        live.add(name)
        if name in rows:
            for value in rows[name][2:]:
                if isinstance(value, str):
                    visit(value)
    visit(packet['output'])
    require(set(rows) <= live, 'Dead arithmetic row')
    require(set(leaves) <= live, 'Unused input or coefficient')
    count = len(set(rows) & live)
    require(count == packet['operations'], 'Incorrect declared live operation count')
    return count


def main():
    ledger = json.loads((HERE / 'LATE_BASELINE_NOTE.json').read_text())
    results, negatives = [], []
    for item in ledger['evidence']:
        name = item['saved']
        path = PurePosixPath(name)
        require(not path.is_absolute() and '..' not in path.parts and chr(92) not in name,
                'Unsafe evidence path')
        raw = (HERE / name).read_bytes()
        require(len(raw) == item['bytes'] and hashlib.sha256(raw).hexdigest() == item['sha256'],
                'Source digest/size mismatch: ' + name)
        result = {'file': name, 'sha256': item['sha256'], 'size_and_digest_verified': True}
        if 'independently_counted_live_operations' in item:
            packet = json.loads(raw)
            count = count_graph(packet)
            require(count == item['independently_counted_live_operations'], 'Ledger count mismatch')
            require(len(packet['witnesses']) == item['variables'], 'Variable count mismatch')
            require(packet['exact_degree'] == item['reported_exact_degree'], 'Reported degree mismatch')
            result.update(live_binary_operations=count, variables=len(packet['witnesses']),
                          source_reported_degree=packet['exact_degree'],
                          degree_reproved_here=False)
            for label in ('count', 'operation', 'missing_gate'):
                bad = copy.deepcopy(packet)
                if label == 'count':
                    bad['operations'] -= 1
                elif label == 'operation':
                    bad['source'][-1][1] = 'divide'
                else:
                    bad['source'].pop(0)
                try:
                    count_graph(bad)
                except ValueError:
                    negatives.append(name + ': ' + label)
                else:
                    raise ValueError('Malformed comparator was accepted')
        results.append(result)
    print(json.dumps({'status': 'PASS', 'construction_pin': ledger['initial_construction_pin'],
                      'late_comparator_pin': ledger['late_review_pin'],
                      'scope': 'Local source hashes and inert live-operation traversal only; no source program execution or new degree/semantic proof.',
                      'verified_evidence': results, 'rejected_mutations': negatives}, indent=2))


if __name__ == '__main__':
    main()
