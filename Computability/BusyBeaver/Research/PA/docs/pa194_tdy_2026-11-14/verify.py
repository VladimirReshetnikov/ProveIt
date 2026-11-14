#!/usr/bin/env python3
"""Reconstruct PA194TDY and check all source-step contracts and its exact startup.

Python 3.10+, standard library only. This is an executable certificate checker,
not a Lean proof. The symbolic register oracles use the unchanged arithmetic
block contracts cited in the report and included in reference/Runtime.lean.
"""
from pathlib import Path
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'reference'))
import symbolic_runtime as s

PHYSICAL = [6, 3, 0, 4, 5, 7, 8, 2, 1]
EDITS = {(41, 1): (0, True, 48), (61, 1): (0, True, 48),
         (82, 1): (0, True, 25), (144, 1): (0, True, 33)}
HASHES = {
    'reference/pa194.tm': '4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f',
    'artifacts/pa194_tdy.native.tm': '2f6e2342151be7c9f7fb8025f81063525c5d276605d2fa87535a9c7d1498755d',
    'artifacts/pa194_tdy.tm': '84bfe1368312c7c71c9e4706de7cb65923310e25f8d472997c9c57c5aedd7934',
    'source/sites.json': 'ffe8ee6395f33ec552a3df23b910aaa16a41060bdd6d55c6189df98d66f30b19',
    'source/instructions.json': '6c3127cd0da15fda49ed99cea199a009b9bc1e1707100846df9a2df02a22d507',
    'reference/symbolic_runtime.py': '955c4d2e8ffaae6d4b3a16d0c91ec54799eaf69ddf40b5686316763272698eeb',
}

def require(condition, message):
    if not condition:
        raise AssertionError(message)

def read_table(path):
    rows = {}
    for line in path.read_text().splitlines():
        if not line.strip() or line.startswith('#'):
            continue
        q, b, w, d, n = line.split()
        q, b, w, n = map(int, (q, b, w, n))
        require((q, b) not in rows and b in (0, 1) and w in (0, 1)
                and d in ('L', 'R'), 'Malformed transition')
        rows[q, b] = w, d == 'R', n
    return rows

def table_text(rows):
    return ''.join(f'{q} {b} {w} {"R" if d else "L"} {n}\n'
                   for (q, b), (w, d, n) in sorted(rows.items()))

def source_contracts(sites):
    by_path = {p: i for i, (p, _, _) in enumerate(sites)}
    def locate(p):
        if p in by_path:
            return by_path[p]
        for i, (q, _, _) in enumerate(sites):
            if q.startswith(p) or (p.startswith(q) and '1' not in p[len(q):]):
                return i
        raise AssertionError(('missing site', p))
    def after(p):
        for i in range(len(p) - 1, -1, -1):
            if p[i] == '0':
                return locate(p[:i] + '1')
        raise AssertionError(('source exit', p))
    def cut(p, bit, k):
        for i in range(len(p) - 1, -1, -1):
            if p[i] == bit:
                k -= 1
                if not k:
                    return p[:i]
        raise AssertionError(('source cut', p, bit))
    instructions, contracts = [], []
    def frame(p, extra=0, effect=s.PLAIN):
        return s.frame(tuple(map(int, p)), extra, effect)
    for i, (p, op, arg) in enumerate(sites):
        if op == 'inc':
            ins = ['inc', arg, after(p)]
        elif op == 'dec':
            ins = ['dec', arg, after(cut(p, '0', 1)), after(p)]
        elif op == 'breakTo':
            ins = ['jump', after(cut(p, '0', arg))]
        elif op == 'continueTo':
            ins = ['jump', locate(cut(p, '1', arg))]
        elif op == 'halt':
            ins = ['halt']
        else:
            raise AssertionError(op)
        instructions.append(ins)
        start = frame(p)
        if ins[0] == 'inc':
            target = s.canonical(frame(sites[ins[2]][0], 0, ('x', 'inc', PHYSICAL[arg])))
            contracts.append((i, None, start, target))
        elif ins[0] == 'dec':
            contracts.append((i, (PHYSICAL[arg], True), start,
                              s.canonical(frame(sites[ins[2]][0]))))
            contracts.append((i, (PHYSICAL[arg], False), start,
                              s.canonical(frame(sites[ins[3]][0], 1,
                                                ('x', 'dec', PHYSICAL[arg])))))
        elif ins[0] == 'jump':
            contracts.append((i, None, start, s.canonical(frame(sites[ins[1]][0]))))
        else:
            contracts.append((i, None, start, None))
    return instructions, contracts

def startup(rows, path):
    physical = [0, 0, 0, 0, 0, 0, 2, 0, 0] + [1] * 26
    expected = {-3, 46}
    expected.update(-2 + i for i, b in enumerate(path) if b == '1')
    pos = 47
    for value in physical:
        pos += 1
        expected.update(range(pos, pos + value + 1))
        pos += value + 1
    q, head, ones = 74, 0, set()
    for step in range(1, 100001):
        w, d, q = rows[q, int(head in ones)]
        (ones.add if w else ones.discard)(head)
        head += 1 if d else -1
        require(q != 254, 'Halted during startup')
        if q == 84 and head == -2 and ones == expected:
            return dict(steps=step, state=q, head=head, complete_tape_equality=True,
                        one_cells=sorted(ones), physical_file=physical)
    raise AssertionError('Exact initialized source frame not reached')

def main():
    for path, wanted in HASHES.items():
        require(hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == wanted,
                'Hash mismatch: ' + path)
    labels = json.loads((ROOT / 'reference/pa194.labels.json').read_text())
    baseline = {(labels[q], b): (w, d, labels[n])
                for (q, b), (w, d, n) in read_table(ROOT / 'reference/pa194.tm').items()}
    rows = baseline | EDITS
    require(table_text(rows) == (ROOT / 'artifacts/pa194_tdy.native.tm').read_text(),
            'Four-row reconstruction differs')
    require(all(rows[q, b] == baseline[q, b] for q in s.BOXSTATES for b in (0, 1)),
            'An arithmetic block changed')
    controls = {q for q, _ in rows}
    require(len(controls) == 194 and len(rows) == 388 and 254 not in controls,
            'Wrong state count')
    require(all((q, b) in rows for q in controls for b in (0, 1)), 'Incomplete table')
    require({n for _, _, n in rows.values()} - controls == {254}, 'Wrong halt label')
    order, ix = [74], {74: 0}
    for q in order:
        for b in (0, 1):
            n = rows[q, b][2]
            if n != 254 and n not in ix:
                ix[n] = len(order)
                order.append(n)
    require(len(order) == 194, 'A working control is graph-unreachable')
    dense = {(ix[q], b): (w, d, 194 if n == 254 else ix[n])
             for (q, b), (w, d, n) in rows.items()}
    require(table_text(dense) == (ROOT / 'artifacts/pa194_tdy.tm').read_text(),
            'Dense table differs')
    require(order + [254] == json.loads((ROOT / 'artifacts/labels.json').read_text()),
            'Label map differs')
    sites = json.loads((ROOT / 'source/sites.json').read_text())
    instructions, contracts = source_contracts(sites)
    require(instructions == json.loads((ROOT / 'source/instructions.json').read_text()),
            'Resolved source graph differs')
    require(len(sites) == 3673 and len(contracts) == 4780, 'Wrong source interface')
    symbolic = s.validate(rows, contracts)
    require(symbolic == {'ok': True, 'contracts': 4780, 'max_steps': 497,
                         'total_steps': 1479348}, 'Symbolic source contract failed')
    boot = startup(rows, sites[25][0])
    require(boot['steps'] == 57594, 'Startup duration differs')
    receipt = dict(working_states=194, transition_rows=388, graph_reachable=194,
                   source_sites=len(sites), logical_to_physical=PHYSICAL,
                   all_box_rows_unchanged=True, symbolic=symbolic, startup=boot,
                   sha256=HASHES, proof_scope='Executable certificates with inherited unchanged arithmetic-block lemmas; not an end-to-end Lean proof')
    print(json.dumps(receipt, indent=2))

if __name__ == '__main__':
    main()
