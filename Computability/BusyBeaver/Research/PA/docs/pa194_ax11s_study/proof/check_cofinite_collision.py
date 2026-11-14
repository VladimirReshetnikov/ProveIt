#!/usr/bin/env python3
"""Exact finite K/S certificate instances of the cofinite-label obstruction.

The all-cutoff proof is in cofinite_collision.tex. K/S are explicitly
inherited derived rules of the restricted implication basis; this program
does not claim to recompile the generic Lean derivations.
"""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def need(claim, message):
    if not claim:
        raise AssertionError(message)


def p(a, b):
    return (a + b) * (a + b + 1) // 2 + b


def I(a, b):
    return 3 * p(a, b)


def U(d, a):
    return 3 * p(a, d) + 2


def E(a, b):
    return 3 * p(a, b) + 3


def K(a, b):
    return I(a, I(b, a))


def S(a, b, c):
    return I(I(a, I(b, c)), I(I(a, b), I(a, c)))


def certificate(cutoff):
    proof = []

    def add(rule, args, conclusion):
        proof.append({'rule': rule, 'args': list(args), 'conclusion': conclusion})
        return len(proof) - 1

    def mp(major, minor, conclusion):
        return add('mp', (major, minor), conclusion)

    def identity(x):
        xx = I(x, x)
        a = add('K', (x, xx), K(x, xx))
        b = add('K', (x, x), K(x, x))
        c = add('S', (x, xx, x), S(x, xx, x))
        return mp(mp(c, a, I(K(x, x), xx)), b, xx)

    T = cutoff + 1
    A = I(T, T)
    B = I(A, 1)
    h, d = A + 1, B - 1
    D = I(A, B)
    need(E(h, d) == D and h >= cutoff and d >= cutoff, 'collision and bounds')
    aa = identity(T)
    dd = identity(D)
    P = I(D, A)
    pp = mp(add('K', (A, D), K(A, D)), aa, P)
    r = add('S', (D, A, B), S(D, A, B))
    q = mp(mp(r, dd, I(P, I(D, B))), pp, I(D, B))
    r = add('S', (D, A, 1), S(D, A, 1))
    neg = mp(mp(r, q, I(P, I(D, 1))), pp, I(D, 1))
    universal = add('gen', (d, neg), U(d, I(D, 1)))
    head = add('head5', (d, h), I(U(d, I(E(h, d), 1)), 1))
    mp(head, universal, 1)
    return proof, {'L': cutoff, 'T': T, 'A': A, 'B': B, 'h': h, 'd': d, 'collision': D}


def check(proof, cutoff):
    values = []
    for index, row in enumerate(proof):
        rule, args, conclusion = row['rule'], row['args'], row['conclusion']
        def previous(j):
            need(0 <= j < index, 'back-reference')
            return values[j]
        if rule == 'K':
            need(conclusion == K(*args), 'K')
        elif rule == 'S':
            need(conclusion == S(*args), 'S')
        elif rule == 'mp':
            need(previous(args[0]) == I(previous(args[1]), conclusion), 'modus ponens')
        elif rule == 'gen':
            need(args[0] >= cutoff, 'allowed binder')
            need(conclusion == U(args[0], previous(args[1])), 'generalization')
        elif rule == 'head5':
            d, h = args
            need(d >= cutoff and h >= cutoff, 'allowed head5')
            need(conclusion == I(U(d, I(E(h, d), 1)), 1), 'head5')
        else:
            raise AssertionError(rule)
        values.append(conclusion)
    need(values[-1] == 1, 'final contradiction')


def main():
    summaries, sample = [], None
    for cutoff in (0, 1, 2, 3, 10, 100, 1000, 1000000):
        proof, values = certificate(cutoff)
        check(proof, cutoff)
        data = json.dumps(proof, sort_keys=True, separators=(',', ':')).encode()
        summaries.append({'cutoff': cutoff, 'proof_lines': len(proof),
                          'certificate_sha256': hashlib.sha256(data).hexdigest(),
                          'parameters': values})
        if cutoff == 10:
            sample = proof
    (HERE / 'cofinite_collision_sample.json').write_text(json.dumps(sample, indent=2) + '\n')
    report = {'status': 'PASS', 'all_cutoff_argument': 'proof/cofinite_collision.tex',
              'instances': summaries,
              'derived_rule_dependencies': ['M6.Logic.RestrictedImplication.k',
                                            'M6.Logic.RestrictedImplication.s'],
              'scope': 'Exact arithmetic instances of a uniform finite derived-rule certificate; not a new Lean build.'}
    (HERE / 'cofinite_collision_check.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
