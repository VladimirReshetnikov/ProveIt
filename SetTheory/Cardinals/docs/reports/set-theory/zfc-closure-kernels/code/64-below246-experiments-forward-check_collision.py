#!/usr/bin/env python3
"""Independent literal witnesses for the branch-information collision.

The universal statement is a corollary of prove_forward_carry.py. This file
separately checks exact finite configurations with a plain sparse simulator.
"""
from pathlib import Path
import hashlib
import json
import os

HERE = Path(__file__).resolve().parent
BASE = Path(os.environ.get('ZFC246_BASE', str(HERE.parents[1] / 'context246' / 'zfc-context246')))


def table():
    source = BASE / 'machine' / 'zfc_prefix246_old.tm'
    assert hashlib.sha256(source.read_bytes()).hexdigest() == '303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee'
    t = {}
    for row in source.read_text().splitlines():
        if not row or row.startswith('#'):
            continue
        q, b, w, d, n = row.split()
        t[int(q), int(b)] = int(w), 1 if d == 'R' else -1, int(n)
    t[255, 0] = 1, -1, 63
    t[255, 1] = 0, 1, 95
    for q in (112, 131):
        for b in (0, 1):
            del t[q, b]
    return t


def blocks(values):
    return [b for v in values for b in [0] + [1]*(v+1)]


def run(t, value, suffix, left):
    word = [0, 0] + [1]*value + blocks(suffix)
    ones = set(left) | {i for i, b in enumerate(word) if b}
    q, h = 95, 0
    trace = []
    for step in range(1000):
        trace.append({'step': step, 'state': q, 'head': h, 'ones': sorted(ones)})
        if step and q == 48 and h == 0:
            return trace
        w, d, q = t[q, int(h in ones)]
        if w:
            ones.add(h)
        else:
            ones.discard(h)
        h += d
    raise AssertionError('Macro did not finish.')


def main():
    if not __debug__:
        raise SystemExit('Assertions are required; do not use -O.')
    t = table()
    assert len(t) == 488
    examples = []
    for name, suffix in [('smallest_nonempty_suffix', [0]),
                         ('nine_primary_registers_plus_spares', [0]*9),
                         ('nine_primary_registers_all_spares_one', [0]*8+[1])]:
        left = {-3, -2, -1}
        zero = run(t, 0, suffix, left)
        positive = run(t, 1, suffix+[1], left)
        expected_word = [1] + blocks([0]+suffix+[1])
        expected = {'state': 48, 'head': 0,
                    'ones': sorted(left | {i for i, b in enumerate(expected_word) if b})}
        assert {k: zero[-1][k] for k in expected} == expected
        assert {k: positive[-1][k] for k in expected} == expected
        assert zero[0]['ones'] != positive[0]['ones']
        examples.append({'name': name, 'zero_input': {'selected': 0, 'suffix': suffix},
                         'positive_input': {'selected': 1, 'suffix': suffix+[1]},
                         'common_endpoint': expected, 'zero_trace': zero, 'positive_trace': positive})
    machine = '#! start 95\n# INCOMPLETE EXPERIMENT: conditional branch information is lost.\n'
    machine += ''.join(f'{q} {b} {w} {"R" if d == 1 else "L"} {n}\n'
                       for (q, b), (w, d, n) in sorted(t.items()))
    (HERE / 'incomplete_forward244_old.tm').write_text(machine)
    out = {'status': 'PASS', 'machine_status': 'INCOMPLETE',
           'claim': 'Two admissible marked files requiring different conditional branches reach the identical full configuration.',
           'scope': 'Precludes recovering the original branch after the collision by a common deterministic return rule. Does not refute all existential many-step simulations or prove a state lower bound.',
           'examples': examples}
    (HERE / 'collision.json').write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps({'status': 'PASS', 'examples': [
        {'name': e['name'], 'zero_steps': len(e['zero_trace'])-1,
         'positive_steps': len(e['positive_trace'])-1,
         'endpoint': e['common_endpoint']} for e in examples]}, indent=2))


if __name__ == '__main__':
    main()
