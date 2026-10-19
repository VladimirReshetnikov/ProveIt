#!/usr/bin/env python3
"""Apply the same raw-assignment interpretation to the frozen six-function kernel.

The source is the exact named-Qd native payload from the prior incoming frozen
kernel. Remove its final Eq(q,I(d,d)) definition, retain the thirteen/fourteen
native rows, and append the four selective-equality clauses. The proof is in
the frozen-kernel corollary of selective_equality.tex. This is a measured input
for a compiler, not a binary machine or state claim.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path

import selective_equality as S

HERE = Path(__file__).resolve().parent
FUNCTIONS = [('V', 2), ('C', 3), ('I', 2), ('A', 2), ('U', 2), ('F', 2)]
PREDICATES = ['E', 'Inc', 'Eq']


def freeze(x):
    return tuple(freeze(a) for a in x) if isinstance(x, list) else x


def run(output):
    output.mkdir(exist_ok=True, parents=True)
    results = {'scope': 'Frozen-core corollary; exact finite payloads, no TM state count', 'theories': {}}
    for extensional, original in [(False, 'FC14Qd_native'), (True, 'FC15Qd_native')]:
        source = HERE / 'reference' / (original + '.json')
        raw = json.loads(source.read_text())
        rows = [[freeze(literal) for literal in row] for row in raw]
        assert rows[-1] == [(True, 'Eq', ('q',), ('I', ('d',), ('d',)))]
        rows = rows[:-1] + S.completion()
        bits = S.encode_payload(rows, True, FUNCTIONS, PREDICATES)
        assert S.decode_payload(bits, True, FUNCTIONS, PREDICATES) == S.X._canonical(rows)
        name = 'frozen_se18' if extensional else 'frozen_se17'
        (output / (name + '.json')).write_text(json.dumps(rows, indent=2) + '\n')
        (output / (name + '.bits')).write_text(bits + '\n')
        padded = bits + '0' * (-len(bits) % 8)
        (output / (name + '.bin')).write_bytes(int(padded, 2).to_bytes(len(padded) // 8, 'big'))
        results['theories'][name] = {
            **S.metrics(rows, True, FUNCTIONS, PREDICATES),
            'source': original + '.json',
            'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
            'independent_payload_roundtrip': True,
        }
    assert results['theories']['frozen_se17']['clauses'] == 17
    assert results['theories']['frozen_se17']['literals'] == 36
    assert results['theories']['frozen_se18']['clauses'] == 18
    assert results['theories']['frozen_se18']['literals'] == 40
    (output / 'frozen_results.json').write_text(json.dumps(results, indent=2) + '\n')
    return results


if __name__ == '__main__':
    print(json.dumps(run(HERE / 'results'), indent=2))
