#!/usr/bin/env python3
"""Independent exact execution of the literal 219-node program's entry prefix.

Compares structured leaf execution with the arithmetic absorption formula.
This is finite regression evidence, supplementary to DirtyRoot254.lean.
No large formula code is built and no proof of contradiction is searched.
"""
from pathlib import Path
from itertools import product
from math import isqrt
import argparse, hashlib, json, random, re, time

EXPECTED_DAG_SHA256 = '538ddaddd932058c2b319011126579d77783231f54331772377c05848a0599e3'

def pairing(x, y):
    return (x+y)*(x+y+1)//2+y

def unpairing(z):
    k = (isqrt(8*z+1)-1)//2
    y = z-k*(k+1)//2
    return k-y, y

def read_nodes(path):
    text = path.read_text()
    def edge(value):
        match = re.fullmatch(r'E(Node|Inc|Decnz|Break|Continue) (\d+)', value)
        if match:
            return match.group(1), int(match.group(2))
        if value == 'EHalt':
            return 'Halt', 0
        raise ValueError(value)
    nodes = {int(m[1]): (edge(m[2]), edge(m[3])) for m in
             re.finditer(r'\| (\d+) => \(([^,]+), ([^)]+)\)', text)}
    if len(nodes) != 219:
        raise ValueError('expected the pinned 219-node program')
    return nodes

def prefix(nodes, initial):
    registers = list(initial)
    atomic_steps = 0
    def execute(edge):
        nonlocal atomic_steps
        tag, operand = edge
        if tag != 'Node':
            atomic_steps += 1
            if atomic_steps > 1000000:
                raise RuntimeError('finite diagnostic fuel exhausted')
            if tag == 'Inc':
                registers[operand] += 1
                return 'normal', 0
            if tag == 'Decnz':
                if registers[operand]:
                    registers[operand] -= 1
                    return 'normal', 0
                return 'break', 1
            if tag == 'Break':
                return ('normal', 0) if operand == 0 else ('break', operand)
            if tag == 'Continue':
                if operand < 1:
                    raise ValueError('zero continue')
                return 'continue', operand
            return 'halt', 0
        first, second = nodes[operand]
        while True:
            kind, count = execute(first)
            if kind == 'break':
                return ('normal', 0) if count == 1 else ('break', count-1)
            if kind != 'normal':
                return kind, count
            kind, count = execute(second)
            if kind == 'continue':
                if count == 1:
                    continue
                return kind, count-1
            return kind, count
    # These are the first two literal routines at root0: fetch133, read174.
    for node in (133, 174):
        if execute(('Node', node)) != ('normal', 0):
            raise AssertionError('entry prefix did not return normally')
    return registers, atomic_steps

def absorption(initial):
    N,T,W,A,D,H,X,Y,L = initial
    n, newN, seedX = (N,N+X+1,0) if L == 0 else (L-1,N,X)
    u,v = unpairing(pairing(seedX,Y)+n)
    m = pairing(A+u,v)
    virtual = [newN,T,W,0,D,H,0,0,m+1]
    endpoint = [newN,T,W,A+u,D,H,0,0,v]
    return virtual, endpoint

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('dag', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if not __debug__:
        raise SystemExit('run without -O')
    nodes = read_nodes(args.dag)
    digest = hashlib.sha256(args.dag.read_bytes()).hexdigest()
    if digest != EXPECTED_DAG_SHA256:
        raise SystemExit('the DAG is not the exact pinned source audited in this report')
    started = time.monotonic()
    counts = {'exhaustive': 0, 'seeded_random': 0}
    maximum = {'dirty_steps': 0, 'virtual_steps': 0}
    failures_of_wrong_formula = {'discard_original_scratch': 0, 'forget_fetch_carry': 0,
                                 'forget_additive_selector': 0}
    examples = []
    rng = random.Random(25320261016)
    cases = [('exhaustive', list(v)) for v in product(range(4), repeat=6)]
    cases += [('seeded_random', [rng.randrange(32) for _ in range(6)]) for _ in range(1000)]
    for kind, (N,A,D,X,Y,L) in cases:
        initial = [N,17,23,A,D,29,X,Y,L]
        virtual, expected = absorption(initial)
        dirty, ds = prefix(nodes, initial)
        clean, cs = prefix(nodes, virtual)
        assert dirty == clean == expected, (initial, dirty, clean, expected)
        counts[kind] += 1
        maximum['dirty_steps'] = max(maximum['dirty_steps'], ds)
        maximum['virtual_steps'] = max(maximum['virtual_steps'], cs)
        n = N if L == 0 else L-1
        u0,v0 = unpairing(n)
        if dirty[3:4]+dirty[8:9] != [A+u0,v0]:
            failures_of_wrong_formula['discard_original_scratch'] += 1
        if L == 0 and dirty[0] != N+1:
            failures_of_wrong_formula['forget_fetch_carry'] += 1
        if dirty[3] != expected[3]-A:
            failures_of_wrong_formula['forget_additive_selector'] += 1
        if len(examples) < 6 and X and Y and A and (L == 0 or len(examples) >= 3):
            examples.append({'initial': initial, 'virtual': virtual, 'endpoint': expected,
                             'dirty_steps': ds, 'virtual_steps': cs})
    assert all(failures_of_wrong_formula.values())
    output = {'status':'PASS', 'dag_sha256':digest,
              'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'arithmetic':'exact unbounded Python integers',
              'entry_nodes':[133,174], 'case_counts':counts,
              'maximum_leaf_steps':maximum, 'negative_control_detections':failures_of_wrong_formula,
              'examples':examples, 'seconds':time.monotonic()-started,
              'scope':'finite prefix regression; universal dirty-prefix equality is separately checked in Lean'}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps(output,indent=2))

if __name__ == '__main__':
    main()
