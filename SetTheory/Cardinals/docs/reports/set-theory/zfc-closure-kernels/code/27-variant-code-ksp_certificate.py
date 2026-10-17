#!/usr/bin/env python3
"""Build/replay a finite K,S,Peirce derivation of the Lukasiewicz schema.

The builder uses the deduction theorem, with ordinary K/S bracket abstraction.
The independent replay routine accepts only exact axiom instances and earlier
modus-ponens parents. No theorem prover, Boolean oracle or assumption rule is
trusted by replay. All validation uses exceptions and remains active under -O.
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
from dataclasses import dataclass
from pathlib import Path

BASE = Path(__file__).resolve().parents[1]

def imp(a, b):
    return (a, b)

def axiom(kind, args):
    if kind == 'K' and len(args) == 2:
        a, b = args
        return imp(a, imp(b, a))
    if kind == 'S' and len(args) == 3:
        a, b, c = args
        return imp(imp(a, imp(b, c)), imp(imp(a, b), imp(a, c)))
    if kind == 'Peirce' and len(args) == 2:
        a, b = args
        return imp(imp(imp(a, b), a), a)
    raise ValueError('unknown axiom or arity')

@dataclass(frozen=True)
class Proof:
    statement: object
    kind: str
    children: tuple = ()
    args: tuple = ()
    label: str = ''

def ax(kind, *args):
    return Proof(axiom(kind, args), kind, args=tuple(args))

def mp(major, minor):
    if not isinstance(major.statement, tuple) or major.statement[0] != minor.statement:
        raise ValueError('invalid generator MP')
    return Proof(major.statement[1], 'MP', (major, minor))

def assumption(label, statement):
    return Proof(statement, 'assumption', label=label)

def free_labels(p):
    if p.kind == 'assumption':
        return {p.label}
    return set().union(*(free_labels(q) for q in p.children))

def identity(a):
    k1 = ax('K', a, imp(a, a))
    k2 = ax('K', a, a)
    s = ax('S', a, imp(a, a), a)
    return mp(mp(s, k1), k2)

def discharge(p, label, hypothesis):
    cache = {}
    def visit(q):
        if q in cache:
            return cache[q]
        if label not in free_labels(q):
            r = mp(ax('K', q.statement, hypothesis), q)
        elif q.kind == 'assumption':
            if q.label != label or q.statement != hypothesis:
                raise ValueError('inconsistent assumption label')
            r = identity(hypothesis)
        elif q.kind == 'MP':
            major, minor = q.children
            s = ax('S', hypothesis, minor.statement, q.statement)
            r = mp(mp(s, visit(major)), visit(minor))
        else:
            raise ValueError('bad abstraction node')
        cache[q] = r
        return r
    return visit(p)

def build():
    p, q, r, s = 'p', 'q', 'r', 's'
    htype, ftype, gtype = imp(p, q), imp(imp(p, q), r), imp(r, p)
    f, g, h = (assumption('f', ftype), assumption('g', gtype),
               assumption('h', htype))
    derived = mp(g, mp(f, h))
    derived = discharge(derived, 'h', htype)
    derived = mp(ax('Peirce', p, q), derived)
    for label, typ in [('s', s), ('g', gtype), ('f', ftype)]:
        derived = discharge(derived, label, typ)
    target = imp(ftype, imp(gtype, imp(s, p)))
    if derived.statement != target or free_labels(derived):
        raise ValueError('builder did not close the target')
    rows, ids = [], {}
    def serialize(x):
        if x in ids:
            return ids[x]
        if x.kind == 'assumption':
            raise ValueError('undischarged assumption')
        children = [serialize(c) for c in x.children]
        item = {'id': len(rows), 'statement': x.statement, 'rule': x.kind}
        if x.kind == 'MP':
            item['parents'] = children
        else:
            item['arguments'] = x.args
        rows.append(item)
        ids[x] = item['id']
        return item['id']
    root = serialize(derived)
    return {'format': 'ksp-finite-proof-v1', 'variables': [p, q, r, s],
            'rows': rows, 'root': root, 'target': target}

def tree(x, variables):
    if isinstance(x, str) and x in variables:
        return x
    if isinstance(x, (tuple, list)) and len(x) == 2:
        return (tree(x[0], variables), tree(x[1], variables))
    raise ValueError('malformed formula')

def replay(data):
    if data.get('format') != 'ksp-finite-proof-v1':
        raise ValueError('wrong format')
    variables = data.get('variables')
    if variables != ['p', 'q', 'r', 's']:
        raise ValueError('wrong variables')
    statements, counts = [], {}
    rows = data.get('rows')
    if not isinstance(rows, list) or not rows:
        raise ValueError('missing rows')
    for i, row in enumerate(rows):
        if row.get('id') != i:
            raise ValueError('invalid row index')
        statement = tree(row.get('statement'), variables)
        rule = row.get('rule')
        if rule == 'MP':
            parents = row.get('parents')
            if (not isinstance(parents, list) or len(parents) != 2 or
                any(type(j) is not int or not 0 <= j < i for j in parents)):
                raise ValueError('MP requires two strictly earlier parents')
            major, minor = [statements[j] for j in parents]
            if major != (minor, statement):
                raise ValueError('MP structural mismatch')
        else:
            args = row.get('arguments')
            if not isinstance(args, (tuple, list)):
                raise ValueError('missing axiom arguments')
            args = [tree(x, variables) for x in args]
            if axiom(rule, args) != statement:
                raise ValueError('wrong axiom instance')
        statements.append(statement)
        counts[rule] = counts.get(rule, 0) + 1
    p, q, r, s = variables
    expected = imp(imp(imp(p, q), r), imp(imp(r, p), imp(s, p)))
    root = data.get('root')
    if type(root) is not int or not 0 <= root < len(rows):
        raise ValueError('invalid root')
    if tree(data.get('target'), variables) != expected or statements[root] != expected:
        raise ValueError('wrong target')
    return {'rows': len(rows), 'counts': counts, 'root': root,
            'target': 'CCCpqrCCrpCsp', 'all_assumptions_discharged': True}

def mutation_checks(data):
    mutations = []
    bad = copy.deepcopy(data); bad['rows'][0]['statement'] = 'p'
    mutations.append(('wrong axiom', bad))
    index = next(i for i, row in enumerate(data['rows']) if row['rule'] == 'MP')
    bad = copy.deepcopy(data); bad['rows'][index]['parents'][0] = index
    mutations.append(('self reference', bad))
    bad = copy.deepcopy(data); bad['target'] = ['p', 'q']
    mutations.append(('wrong target', bad))
    result = []
    for name, bad in mutations:
        try:
            replay(bad)
        except ValueError as error:
            result.append({'case': name, 'rejected': True, 'reason': str(error)})
        else:
            raise ValueError('mutation accepted: ' + name)
    return result

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build', action='store_true')
    parser.add_argument('--certificate', type=Path,
                        default=BASE / 'data/lukasiewicz_from_ksp.json')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    if args.build:
        args.certificate.write_text(json.dumps(build(), indent=2) + '\n')
    raw = args.certificate.read_bytes()
    data = json.loads(raw)
    result = replay(data)
    result['sha256'] = hashlib.sha256(raw).hexdigest()
    result['mutations'] = mutation_checks(data)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
