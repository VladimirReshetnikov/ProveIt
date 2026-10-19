#!/usr/bin/env python3
"""Audit an ordered search result against its exact finite input instance.

This validates binary word equations, terminal orientations, physical-entry
projections, supplied bootstrap locks and expanded AST path bounds.  It does
not validate a binary Turing-machine table or prove a global lower bound.
"""
import argparse
import hashlib
import json
from functools import cache
from pathlib import Path


def audit(grammar, constraints, locks, candidate):
    lines = grammar.read_text().splitlines()
    n, nr, na = map(int, lines[0].split())
    old = {}
    for row in lines[1:1+n]:
        k, w, _ = row.split()
        old[w] = (w[:int(k)], w[int(k):])
    roots = lines[1+n:1+n+nr]
    terminals = dict((w, int(m)) for w, m in
                     map(str.split, lines[1+n+nr:]))
    assert len(terminals) == na
    rows = iter(constraints.read_text().splitlines())
    nc = int(next(rows)); projections = []
    for _ in range(nc):
        q, bit, original, count = next(rows).split()
        req = [tuple(next(rows).split()) for _ in range(int(count))]
        projections.append(((int(q), int(bit)), original, req))
    nn, source_root, nat = map(int, next(rows).split())
    nodes = [next(rows).split() for _ in range(nn)]
    atoms = dict((w, int(i)) for w, i in
                 (next(rows).split() for _ in range(nat)))
    assert not any(line.strip() for line in rows)
    data = json.loads(candidate.read_text())
    rules = {w: (a, b) for w, a, b in data['rules']}
    assert len(rules) == len(data['rules']) == data['rules_count']
    for w, (a, b) in rules.items():
        assert a and b and w == a+b
        assert w not in terminals
        for bit, child in enumerate((a, b)):
            assert child in rules or child in terminals
            if child in terminals:
                assert terminals[child] & (1 << bit)
    routes = {(r['source'], r['read']): r['word']
              for r in data['routes']}
    assert len(routes) == len(data['routes']) == nc
    assert all(w in rules or w in terminals for w in roots)

    def project(w, path):
        for bit in path:
            assert w in rules
            w = rules[w][int(bit)]
        return w

    projection_count = 0
    for key, _, req in projections:
        for path, target in req:
            assert project(routes[key], path) == target
            projection_count += 1
    lock_lines = locks.read_text().splitlines()
    checked_locks = 0
    for row in lock_lines[1:]:
        if row.strip():
            w, path, target = row.split()
            assert project(w, path) == target
            checked_locks += 1
    assert checked_locks == int(lock_lines[0])
    visiting = set()

    def join(a, b):
        return (a[0]+1, max(a[0]+1, a[1], b[1]),
                max(a[2], b[2])+1)

    @cache
    def ast(i):
        key = ('ast', i)
        assert key not in visiting, 'cyclic AST/word definitions'
        visiting.add(key)
        row = nodes[i]
        if row[0] == 'L':
            value = (0, 0, 0)
        elif row[0] == 'N':
            value = join(ast(int(row[1])), ast(int(row[2])))
        else:
            assert row[0] == 'W'
            value = word(row[1])
        visiting.remove(key)
        return value

    @cache
    def word(w):
        key = ('word', w)
        assert key not in visiting, 'cyclic AST/word definitions'
        visiting.add(key)
        if w in terminals:
            value = ast(atoms[w])
        else:
            a, b = rules[w] if w in rules else old[w]
            value = join(word(a), word(b))
        visiting.remove(key)
        return value

    properties = ast(source_root)
    assert list(properties) == data['properties'][:3]
    assert properties[1] <= 6
    return {
        'status': 'PASS_FINITE_ORDERED_GRAMMAR_INPUT_AUDIT',
        'rules': len(rules), 'terminal_words': len(terminals),
        'route_projections': projection_count,
        'bootstrap_equations': checked_locks,
        'properties': properties,
        'candidate_sha256': hashlib.sha256(candidate.read_bytes()).hexdigest(),
        'scope': 'Finite input instance only; no literal TM or lower bound.'}


if __name__ == '__main__':
    assert __debug__, 'Run without Python -O: assertions are verification gates.'
    p = argparse.ArgumentParser()
    for name in ('grammar', 'constraints', 'locks', 'candidate'):
        p.add_argument('--'+name, type=Path, required=True)
    p.add_argument('--output', type=Path)
    a = p.parse_args()
    result = audit(a.grammar, a.constraints, a.locks, a.candidate)
    content = json.dumps(result, indent=2)+'\n'
    if a.output:
        a.output.write_text(content)
    print(content, end='')
