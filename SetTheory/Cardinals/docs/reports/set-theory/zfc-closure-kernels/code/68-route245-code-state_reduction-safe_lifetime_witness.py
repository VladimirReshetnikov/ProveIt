#!/usr/bin/env python3
"""Exact source-level trace to a theorem-safe nine-value register phase.

This is an obstruction only to direct pointwise register aliasing for the
unchanged source program on every admitted safe root. It is not a lower bound
on machine states or on alternate register algorithms, nor a blank-run claim.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import re
from pathlib import Path

INITIAL = (4, 0, 3, 0, 6, 2, 0, 0, 1648)
TARGET = (4, 0, 3, 5, 6, 2, 1, 7, 8)
NAMES = ('N', 'T', 'W', 'A', 'D', 'H', 'X', 'Y', 'L')
POSITIVE_INITIAL = (4, 2, 3, 0, 6, 10, 0, 0, 1648)
POSITIVE_TARGET = (4, 2, 3, 5, 6, 10, 1, 7, 8)

def pairing(a, b):
    return (a + b) * (a + b + 1) // 2 + b

def parse_table(text):
    data = text.split('Definition p254_tab', 1)[1].split('[', 1)[1].split('].', 1)[0]
    edge = r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    nodes = re.findall(r'\((' + edge + r'),\s*(' + edge + r')\)', data)
    assert len(nodes) == 6459
    return [[(e.split()[0], int(e.split()[1]) if len(e.split()) == 2 else None)
             for e in row] for row in nodes]

def decode(nodes, pc):
    state, path = 0, ''
    while True:
        bit = pc[len(path)] if len(path) < len(pc) else '0'
        path += bit
        op, arg = nodes[state][int(bit)]
        if op == 'CN':
            state = arg
        else:
            assert '1' not in pc[len(path):]
            return path, op, arg

def successor(path, op, arg, zero):
    def strip(path, bit, count):
        for _ in range(count):
            j = path.rfind(bit)
            path = '' if j < 0 else path[:j]
        return path
    def inc(path):
        j = path.rfind('0')
        return '0' * len(path) if j < 0 else path[:j] + '1' + '0' * (len(path)-j-1)
    if op == 'CI' or op == 'CD' and not zero:
        return inc(path)
    if op == 'CD':
        return inc(strip(path, '0', 1))
    if op == 'CB':
        return inc(strip(path, '0', arg))
    if op == 'CC':
        return strip(path, '1', arg)
    assert op == 'CH'
    return None

def trace(nodes, limit, initial=INITIAL, target=TARGET):
    regs, pc = list(initial), ''
    digest = hashlib.sha256()
    milestones = []
    for step in range(limit + 1):
        path, op, arg = decode(nodes, pc)
        if tuple(regs) == target:
            return {'source_instructions': step, 'counter': pc,
                    'decoded_path': path, 'instruction': [op, arg],
                    'registers': regs, 'trace_sha256': digest.hexdigest(),
                    'milestones': milestones}
        if regs[3] == 5 and regs[6] == regs[7] == 0 and regs[8] == 51:
            if not milestones:
                milestones.append({'source_instructions': step, 'counter': pc,
                                   'decoded_path': path, 'registers': regs[:]})
        record = [step, path, op, arg, regs]
        digest.update((json.dumps(record, separators=(',', ':')) + '\n').encode())
        if op == 'CH':
            raise AssertionError('Unexpected halt')
        zero = op == 'CD' and regs[arg] == 0
        if op == 'CI':
            regs[arg] += 1
        elif op == 'CD' and not zero:
            regs[arg] -= 1
        pc = successor(path, op, arg, zero)
    raise AssertionError('Trace limit exhausted')

def independent_dag_trace(dag_text, limit, initial=INITIAL, target=TARGET):
    """Structured small-step interpreter; no binary path arithmetic is used."""
    edge = r'(?:ENode \d+|EInc \d+|EDecnz \d+|EBreak \d+|EContinue \d+|EHalt)'
    raw = re.findall(r'\| (\d+) => \((' + edge + r'),\s*(' + edge + r')\)', dag_text)
    nodes = {int(n): tuple((e.split()[0], int(e.split()[1]) if len(e.split()) == 2 else None)
                          for e in (a,b)) for n,a,b in raw}
    assert len(nodes) == 219
    regs = list(initial)
    stack = []
    edge = ('ENode', 0)
    ticks = 0
    def go_next():
        nonlocal edge
        while stack:
            n, side = stack.pop()
            if side == 0:
                stack.append((n, 1))
                edge = nodes[n][1]
                return
        edge = ('ENode', 0)
    while ticks <= limit:
        op, arg = edge
        if op == 'ENode':
            stack.append((arg, 0))
            edge = nodes[arg][0]
            continue
        if tuple(regs) == target:
            return {'source_instructions': ticks, 'instruction': [op, arg],
                    'registers': regs, 'control_stack': stack}
        if op == 'EHalt':
            raise AssertionError('Unexpected structured halt')
        if op == 'EInc':
            regs[arg] += 1
            go_next()
        elif op == 'EDecnz' and regs[arg] > 0:
            regs[arg] -= 1
            go_next()
        else:
            if op == 'EDecnz':
                op, arg = 'EBreak', 1
            assert op in ('EBreak', 'EContinue')
            # A break consumes car-level nodes; a continue consumes cdr-level
            # nodes. This is the structured meaning of zero/one path stripping.
            wanted = 0 if op == 'EBreak' else 1
            while arg:
                n, side = stack.pop()
                arg -= side == wanted
            if op == 'EBreak':
                go_next()
            else:
                edge = ('ENode', n)
        ticks += 1
    raise AssertionError('Structured trace limit exhausted')

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--program', type=Path, default=Path(__file__).with_name('Prog254.v'))
    ap.add_argument('--dag', type=Path, required=True)
    ap.add_argument('--output', type=Path, default=Path(__file__).with_name('safe-lifetime-witness.json'))
    args = ap.parse_args()
    raw, dag = args.program.read_bytes(), args.dag.read_bytes()
    assert pairing(2, 0) == 3
    assert pairing(5, 51) + 1 == INITIAL[8]
    assert pairing(1, 7) + 8 == 51
    direct = trace(parse_table(raw.decode()), 2_000_000)
    structured = independent_dag_trace(dag.decode(), 2_000_000)
    assert direct['source_instructions'] == structured['source_instructions']
    assert direct['registers'] == structured['registers'] == list(TARGET)
    assert sorted(TARGET) == list(range(9))
    positive_direct = trace(parse_table(raw.decode()), 2_000_000, POSITIVE_INITIAL, POSITIVE_TARGET)
    positive_structured = independent_dag_trace(dag.decode(), 2_000_000, POSITIVE_INITIAL, POSITIVE_TARGET)
    assert positive_direct['source_instructions'] == positive_structured['source_instructions'] == 13517
    assert positive_direct['registers'] == positive_structured['registers'] == list(POSITIVE_TARGET)
    assert min(POSITIVE_TARGET) > 0 and len(set(POSITIVE_TARGET)) == 9
    result = {'status': 'PASS', 'scope': __doc__, 'logical_register_order': NAMES,
              'initial': INITIAL, 'target': TARGET,
              'program_sha256': hashlib.sha256(raw).hexdigest(),
              'dag_sha256': hashlib.sha256(dag).hexdigest(),
              'path_interpreter': direct, 'structured_interpreter': structured,
              'all_36_pairs_distinct': [[NAMES[i],NAMES[j]] for i in range(9) for j in range(i+1,9)],
              'safety': {'T': '0 = Top', 'H': '2 = All(Top)',
                         'W': '3 = P(2,0), a stack containing All(Top)'},
              'positive_safe_witness': {'initial': POSITIVE_INITIAL, 'target': POSITIVE_TARGET,
                         'path_interpreter': positive_direct,
                         'structured_interpreter': positive_structured,
                         'safety': {'T': '2 = All(Top)', 'H': '10 = All(All(Top))',
                                    'W': '3 = P(2,0), a stack containing All(Top)'}},
              'limitations': ['No blank-run reachability claim.',
                              'No state lower bound.',
                              'No obstruction to packed, recomputed, affine, or phase-specific representations.',
                              'No new candidate machine or new proof-assistant theorem.']}
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k:direct[k] for k in ('source_instructions','counter','decoded_path','registers')}, indent=2))

if __name__ == '__main__':
    main()
