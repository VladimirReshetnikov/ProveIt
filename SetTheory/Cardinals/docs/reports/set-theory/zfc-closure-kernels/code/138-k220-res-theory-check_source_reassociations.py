#!/usr/bin/env python3
"""Independent source-only check of the two winning K221 -> K220 rotations.

Standard library only. This checks syntax, exact source reconstruction, closed
boundaries, the complete primitive word and guarded CFG. It does not check the
binary table, state fold, initialization, or unbounded binary runtime.
"""
import argparse
from functools import lru_cache
import hashlib
import json
from pathlib import Path


def need(ok, message):
    if not ok:
        raise ValueError(message)


def leaf(t):
    return isinstance(t[0], str)


def decode(rows):
    d = {}
    for path, op, arg in rows:
        need(isinstance(path, str) and path and set(path) <= {'0', '1'}, 'bad path')
        need(op in {'CI', 'CD', 'CB', 'CC', 'CH'}, 'bad operation')
        need((op == 'CH' and arg is None) or
             (op != 'CH' and type(arg) is int and arg >= 0), 'bad operand')
        p = d
        for bit in path:
            need('value' not in p, 'overlapping leaf')
            p = p.setdefault(bit, {})
        need(not p, 'duplicate or overlapping leaf')
        p['value'] = (op, arg)
    def walk(p):
        if 'value' in p:
            need(set(p) == {'value'}, 'nonterminal leaf')
            return p['value']
        need(set(p) == {'0', '1'}, 'tree must be full')
        return walk(p['0']), walk(p['1'])
    t = walk(d)
    need(encode(t) == rows, 'noncanonical row order')
    return t


def encode(t, path=''):
    if leaf(t):
        return [[path, *t]]
    return encode(t[0], path+'0') + encode(t[1], path+'1')


@lru_cache(None)
def bound(t):
    if leaf(t):
        op, a = t
        if op == 'CD':
            return 1, 0, False
        if op == 'CB':
            return a, 0, False
        if op == 'CC':
            return 0, a, False
        return 0, 0, op == 'CH'
    a, b = bound(t[0]), bound(t[1])
    return max(a[0]-1, b[0], 0), max(a[1], b[1]-1, 0), a[2] or b[2]


def subtree(t, path):
    for bit in path:
        need(not leaf(t), 'path continues past a leaf')
        t = t[int(bit)]
    return t


def replace(t, path, n):
    if not path:
        return n
    bit = int(path[0])
    p = list(t)
    p[bit] = replace(p[bit], path[1:], n)
    return tuple(p)


def guarded_cfg(rows):
    """Resolve outward control directly through subtree start/end ordinals."""
    positions = {p: i for i, (p, _, _) in enumerate(rows)}
    intervals = {}
    def walk(p):
        if p in positions:
            answer = positions[p], positions[p]+1
        else:
            a, b = walk(p+'0'), walk(p+'1')
            need(a[1] == b[0], 'noncontiguous interval')
            answer = a[0], b[1]
        intervals[p] = answer
        return answer
    count = len(rows)
    need(walk('') == (0, count), 'whole-tree interval')
    def target(p, edge, levels):
        while p:
            last, p = p[-1], p[:-1]
            if last == edge:
                levels -= 1
                if levels == 0:
                    return intervals[p][0 if edge == '1' else 1] % count
        return 0
    result = []
    for i, (p, op, a) in enumerate(rows):
        nxt = (i+1) % count
        if op == 'CI':
            result.append([op, a, [nxt]])
        elif op == 'CD':
            result.append([op, a, [target(p, '0', 1), nxt]])
        elif op == 'CB':
            result.append([op, a, [target(p, '0', a)]])
        elif op == 'CC':
            result.append([op, a, [target(p, '1', a)]])
        else:
            result.append([op, a, []])
    return result


def metrics(t):
    seen = set()
    def walk(n):
        if n in seen:
            return
        seen.add(n)
        if not leaf(n):
            walk(n[0]); walk(n[1])
    walk(t)
    rows = encode(t)
    return {'dag_nodes': len(seen), 'primitive_occurrences': len(rows),
            'maximum_depth': max(len(p) for p, _, _ in rows),
            'maximum_zero_run': max(len(z) for p, _, _ in rows for z in p.split('1'))}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline', type=Path, required=True)
    ap.add_argument('--seed', type=Path, required=True)
    ap.add_argument('--final', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    a = ap.parse_args()
    files = [a.baseline, a.seed, a.final]
    raws = [p.read_bytes() for p in files]
    rows = [json.loads(x) for x in raws]
    trees = [decode(x) for x in rows]
    recipes = [('11101001001101', 'R', (52, 27, 295)),
               ('111010010011011', 'L', (27, 52, 243))]
    report_steps = []
    for old, new, (path, direction, sizes) in zip(trees, trees[1:], recipes):
        n = subtree(old, path)
        if direction == 'R':
            (A, B), C = n
            target = A, (B, C)
        else:
            A, (B, C) = n
            target = (A, B), C
        bounds = [bound(x) for x in (A, B, C)]
        need(bounds == [(0, 0, False)]*3, 'factor not fully closed')
        need(tuple(len(encode(x)) for x in (A, B, C)) == sizes, 'factor size mismatch')
        need(replace(old, path, target) == new, 'unexpected source change')
        report_steps.append({'path': path, 'direction': direction,
                             'factor_leaf_counts': list(sizes), 'boundaries': bounds})
    words = [[x[1:] for x in r] for r in rows]
    need(words[0] == words[1] == words[2], 'primitive word changed')
    graphs = [guarded_cfg(r) for r in rows]
    need(graphs[0] == graphs[1] == graphs[2], 'guarded CFG changed')
    cases = sum(len(x[2]) if x[0] != 'CH' else 1 for x in graphs[0])
    need(cases == 6167, 'guarded case count')
    report = {'status': 'INDEPENDENT_TWO_CLOSED_REASSOCIATIONS_PASS',
              'source_sha256': {name: hashlib.sha256(raw).hexdigest()
                                for name, raw in zip(('baseline', 'seed', 'final'), raws)},
              'steps': report_steps, 'source_metrics': [metrics(t) for t in trees],
              'primitive_word_equal': True, 'guarded_cfg_equal': True,
              'guarded_cases': cases,
              'scope': 'Source syntax and exact full guarded CFG only. Binary decoder binding, primitive runtime, fold, and startup are separate obligations.'}
    a.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
