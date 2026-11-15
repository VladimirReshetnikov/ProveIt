#!/usr/bin/env python3
"""Independent replay of the new universal logical certificates.

K, S and Peirce are explicitly admitted derived rules from the retained rho8
basis. No other propositional oracle, assumption, or unlisted rule is admitted.
"""
from pathlib import Path
import argparse, collections, json


def imp(a, b): return ('I', a, b)
def all_(d, a): return ('U', d, a)
def eq(a, b): return ('E', a, b)
ZERO, FALSE = ('nat', 0), ('nat', 1)
def neg(a): return imp(a, FALSE)
def witness(d, h): return all_(d, neg(eq(h, d)))
def inner(d, h): return all_(d, neg(all_(d, h)))


def need(p, message):
    if not p: raise ValueError(message)


def check(path):
    data = json.loads(path.read_text())
    need(data['format'] == 'universal-hilbert-template-v1', 'format')
    terms = []
    for n, row in enumerate(data['terms']):
        op, *args = row
        if op == 'nat':
            need(len(args) == 1 and type(args[0]) is int and args[0] in (0, 1), 'literal')
            terms.append((op, args[0]))
        elif op == 'parameter':
            need(len(args) == 1 and args[0] in ('A', 'D', 'H'), 'parameter')
            terms.append((op, args[0]))
        else:
            need(op in ('I', 'U', 'E') and len(args) == 2, 'constructor')
            need(all(type(k) is int and 0 <= k < n for k in args), 'term topology')
            terms.append((op, terms[args[0]], terms[args[1]]))
    proofs = []
    counts = collections.Counter()
    basis = {'K', 'S', 'MP'}
    permitted = {
        'old_to_h5X.json': basis | {'h1', 'h5'},
        'h5X_to_old.json': {'h5X'},
        'h5X_explosion.json': basis | {'Gamma', 'h6Q', 'h5X', 'Gen'},
        'coupled_to_h1.json': basis | {'Gamma', 'h6Q', 'h5X', 'Gen', 'dualB', 'Peirce'},
        'h1_to_dualB.json': basis | {'h1', 'Peirce'},
        'ordinary_to_Q.json': basis,
        'Q_to_ordinary.json': basis,
    }
    for n, row in enumerate(data['proofs']):
        rule, args, conclusion = row['rule'], row['args'], row['conclusion']
        need(rule in permitted[path.name], 'rule is unavailable in the claimed source theory: ' + rule)
        need(type(conclusion) is int and 0 <= conclusion < len(terms), 'conclusion index')
        counts[rule] += 1
        if rule == 'MP':
            need(len(args) == 2 and all(type(k) is int and 0 <= k < n for k in args), 'MP topology')
            major, minor = (proofs[k] for k in args)
            need(major[0] == 'I' and major[1] == minor, 'MP equation')
            expected = major[2]
        elif rule == 'Gen':
            need(len(args) == 2 and type(args[0]) is int and 0 <= args[0] < len(terms), 'Gen binder')
            need(type(args[1]) is int and 0 <= args[1] < n, 'Gen topology')
            expected = all_(terms[args[0]], proofs[args[1]])
        else:
            need(all(type(k) is int and 0 <= k < len(terms) for k in args), 'schema index')
            aa = [terms[k] for k in args]
            if rule == 'K':
                a, b = aa; expected = imp(a, imp(b, a))
            elif rule == 'S':
                a, b, c = aa; expected = imp(imp(a, imp(b, c)), imp(imp(a, b), imp(a, c)))
            elif rule == 'Peirce':
                a, b = aa; expected = imp(imp(imp(a, b), a), a)
            elif rule == 'Gamma':
                a, = aa; expected = imp(a, all_(a, a))
            elif rule == 'h6Q':
                d, a, h = aa; expected = imp(all_(d, imp(a, h)), imp(all_(d, a), all_(d, h)))
            elif rule == 'h5':
                d, h = aa; expected = neg(witness(d, h))
            elif rule == 'h5X':
                d, a, h = aa; expected = imp(witness(d, h), a)
            elif rule == 'h1':
                d, h = aa; expected = imp(neg(inner(d, h)), h)
            elif rule == 'dualB':
                d, h = aa; expected = imp(neg(h), inner(d, h))
            else: raise ValueError('unlisted rule: ' + rule)
        need(terms[conclusion] == expected, f'line {n} does not instantiate {rule}')
        proofs.append(expected)
    a, d, h = [('parameter', name) for name in ('A', 'D', 'H')]
    targets = {
        'old_to_h5X.json': imp(witness(d, h), a),
        'h5X_to_old.json': neg(witness(d, h)),
        'h5X_explosion.json': imp(FALSE, a),
        'coupled_to_h1.json': imp(neg(inner(d, h)), h),
        'h1_to_dualB.json': imp(neg(h), inner(d, h)),
    }
    p, q, r = all_(d, a), all_(d, imp(a, h)), all_(d, h)
    ordinary, exchanged = imp(p, imp(q, r)), imp(q, imp(p, r))
    targets.update({'ordinary_to_Q.json': imp(ordinary, exchanged),
                    'Q_to_ordinary.json': imp(exchanged, ordinary)})
    need(type(data['final']) is int and 0 <= data['final'] < len(proofs), 'final index')
    need(proofs[data['final']] == targets[path.name], 'wrong theorem')
    return dict(file=path.name, status='PASS', proof_steps=len(proofs), rules=dict(sorted(counts.items())),
                assumptions=0, truth_table_oracles=0, kernel_checked=False)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    files = ['old_to_h5X.json', 'h5X_to_old.json', 'h5X_explosion.json', 'coupled_to_h1.json', 'h1_to_dualB.json',
             'ordinary_to_Q.json', 'Q_to_ordinary.json']
    result = dict(status='PASS', scope='Universal finite Hilbert templates over explicitly retained derived basis K/S/Peirce',
                  certificates=[check(args.directory / name) for name in files])
    if args.output: args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))
