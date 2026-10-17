#!/usr/bin/env python3
"""Check the final DBM source invariant without running its abstract search.

This checker uses ordinary Python integers and a separate Floyd closure
implementation. It checks every source edge, all concrete branch guards,
initial inclusion, and the exact list of impossible guards. It does not
reuse NumPy or the searcher's transfer code.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'upstream/Computability/BusyBeaver/Research/ZFC'
PROG = ROOT / 'upstream/lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v'
sys.path.insert(0, str(BASE))
import permutation252_phase_analysis as phase

SIZE = 10


def closure(a, infinity):
    a = [r[:] for r in a]
    for k in range(SIZE):
        for i in range(SIZE):
            if a[i][k] == infinity:
                continue
            for j in range(SIZE):
                if a[k][j] != infinity:
                    a[i][j] = min(a[i][j], a[i][k] + a[k][j])
    if any(a[i][i] < 0 for i in range(SIZE)):
        return None
    return a


def check(path):
    record = json.loads(path.read_text())
    infinity = record['infinity_sentinel']
    raw = PROG.read_bytes()
    assert record['program_sha256'] == sha256(raw).hexdigest() == phase.PROG_SHA
    sites, cases, targets, first = phase.program_graph(raw)
    classes = []
    for flat in record['invariant_classes']:
        if flat is None:
            classes.append(None)
        else:
            assert len(flat) == SIZE * SIZE
            a = [flat[i*SIZE:(i+1)*SIZE] for i in range(SIZE)]
            assert all(x <= infinity for r in a for x in r)
            assert all(a[0][i] <= 0 for i in range(SIZE))
            assert all(a[i][i] == 0 for i in range(SIZE))
            assert closure(a, infinity) == a
            classes.append(a)
    assert len(record['site_class_ids']) == len(sites)
    states = [classes[i] for i in record['site_class_ids']]
    assert all(x >= 0 for row in states[first] for x in row)
    impossible, edges = [], 0
    for i, (case, target) in enumerate(zip(cases, targets)):
        site, _, op, r, zero = case
        original = states[site]
        if original is None:
            impossible.append(i)
            continue
        a = [row[:] for row in original]
        if op == 'CD':
            if zero:
                a[r+1][0] = min(a[r+1][0], 0)
            else:
                a[0][r+1] = min(a[0][r+1], -1)
            a = closure(a, infinity)
            if a is None:
                impossible.append(i)
                continue
        if op == 'CI' or op == 'CD' and not zero:
            offsets = [0] * SIZE
            offsets[r+1] = 1 if op == 'CI' else -1
            a = [[infinity if a[x][y] == infinity else
                  a[x][y] + offsets[x] - offsets[y]
                  for y in range(SIZE)] for x in range(SIZE)]
        if target is not None:
            assert states[target] is not None
            assert all(a[x][y] <= states[target][x][y]
                       for x in range(SIZE) for y in range(SIZE)), i
            edges += 1
    assert impossible == record['excluded_guards']
    assert edges == record['exact_postfix_edges_checked']
    return {'certificate': path.name, 'status': 'PASS independent integer checker',
            'classes': len(classes), 'sites': len(sites), 'guards': len(cases),
            'postfix_edges': edges, 'excluded_guards': impossible}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificates', type=Path, nargs='+')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    results = [check(path) for path in args.certificates]
    text = json.dumps(results, indent=2) + '\n'
    if args.output:
        args.output.write_text(text)
    print(text, end='')
