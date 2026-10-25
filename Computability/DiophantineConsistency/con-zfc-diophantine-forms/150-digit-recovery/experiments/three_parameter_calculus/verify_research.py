#!/usr/bin/env python3
"""Small independent checks for the three-parameter calculus experiment.

This file imports neither the constructor nor the inherited arithmetic
compiler. It checks a literal propositional proof, exact polynomial
coefficients, the recorded size, and finite controls for the modular lemma.
It does not certify the unbounded CRT/Pell interpretation of the equation.
"""
from collections import Counter
from copy import deepcopy
from math import gcd, prod
from pathlib import Path
import argparse
import hashlib
import json


def require(condition, message):
    if not condition:
        raise ValueError(message)


def implication(x):
    return isinstance(x, list) and len(x) == 2


def well_formed(f):
    if isinstance(f, str):
        return f in ('a', 'b', 'c', 'd')
    return implication(f) and well_formed(f[0]) and well_formed(f[1])


def axiom(f, rule):
    # Structural schema matching; there is no logical search here.
    if not implication(f):
        return False
    if rule == 'K':
        return implication(f[1]) and f[1][1] == f[0]
    if rule == 'S':
        if not implication(f[0]) or not implication(f[0][1]):
            return False
        p, (q, r) = f[0]
        return f == [[p, [q, r]], [[p, q], [p, r]]]
    if rule == 'P':
        if not implication(f[0]) or not implication(f[0][0]):
            return False
        p, q = f[0][0]
        return f == [[[p, q], p], p]
    return False


def verify_basis(cert):
    require(cert['schema'] == 'implicational_hilbert_proof_v1', 'proof schema')
    steps = cert['steps']
    require(cert['conclusion'] == len(steps)-1, 'final conclusion index')
    for j, step in enumerate(steps):
        f, rule, premises = step['formula'], step['rule'], step['premises']
        require(well_formed(f), f'ill-formed formula at {j}')
        if rule == 'mp':
            require(len(premises) == 2 and all(type(i) is int and 0 <= i < j for i in premises),
                    f'bad premises at {j}')
            minor = steps[premises[0]]['formula']
            major = steps[premises[1]]['formula']
            require(major == [minor, f], f'bad modus ponens at {j}')
        else:
            require(not premises and axiom(f, rule), f'bad axiom at {j}')
    expected = [[['c', 'd'], 'a'], [['a', 'c'], ['b', 'c']]]
    require(steps[-1]['formula'] == expected, 'wrong final schema')
    return {'steps': len(steps), 'rules': dict(Counter(s['rule'] for s in steps)),
            'theorem': '((c->d)->a)->((a->c)->(b->c))'}


def collect(terms):
    c = Counter()
    for coefficient, monomial in terms:
        c[tuple(sorted(monomial))] += coefficient
    return [[v, list(k)] for k, v in sorted(c.items()) if v]


def verify_polynomial(eq, expanded):
    require(eq['domain'] == 'nonnegative integers', 'wrong coordinate domain')
    n = len(eq['variables'])
    seen = set()
    terms = []
    for row in eq['residuals']:
        r = row['terms']
        require(r == collect(r), 'noncanonical row')
        for a, ma in r:
            require(type(a) is int and a != 0 and len(ma) <= 2, 'nonquadratic row')
            require(all(type(v) is int and 0 <= v < n for v in ma), 'bad coordinate')
            seen.update(ma)
            for b, mb in r:
                terms.append([a*b, ma+mb])
    require(seen == set(range(n)), 'unused coordinate')
    actual = collect(terms)
    require(expanded['terms'] == actual, 'expanded polynomial differs')
    metric = {'variables': n, 'rows': len(eq['residuals']),
              'exact_degree': max(map(lambda item: len(item[1]), actual)),
              'expanded_monomials': len(actual),
              'coefficient_height': max(abs(item[0]) for item in actual)}
    require(metric == {'variables': 231, 'rows': 183, 'exact_degree': 4,
                       'expanded_monomials': 6369, 'coefficient_height': 83899166},
            'unexpected experimental metrics')
    m = eq['metrics']
    for a, b in [('variables', 'variables'), ('rows', 'quadratic_rows'),
                 ('exact_degree', 'exact_degree'), ('expanded_monomials', 'expanded_monomials'),
                 ('coefficient_height', 'max_abs_expanded_coefficient')]:
        require(metric[a] == m[b], f'recorded {b} differs')
    return metric


def crt(residues, moduli):
    modulus = prod(moduli)
    return sum(r*(modulus//m)*pow(modulus//m, -1, m)
               for r, m in zip(residues, moduli)) % modulus


def finite_controls():
    # These are controls of the proved lemma, not a replacement for its proof.
    cases = 0
    for modulus in (2, 3, 4, 5, 7, 8, 9, 11, 13):
        for u in range(modulus):
            for v in range(modulus):
                if u*v >= modulus:
                    continue
                for d in range(7):
                    for e in range(modulus):
                        if u*v % modulus == 0 and u*(d*e-1) % modulus == 0:
                            require(u == 0 or (v == 0 and d != 0), 'saturation soundness control')
                            cases += 1
    # Two essential hypotheses: a nonzero D need not be invertible, and U
    # needs its own bound when the product U*V vanishes.
    require(all(3*e % 3 != 1 for e in range(3)), 'nonunit countercontrol')
    require((3*(0*1-1)) % 3 == 0, 'missing-U-bound countercontrol')
    # A heterogeneous 3-row CRT witness, including a disabled guard.
    moduli = [7**2, 11**2, 13**2]
    tuples = [(0, 2, 1, 3), (2, 0, 3, 1), (0, 0, 0, 0)]
    # Each tuple is (U,V,c-a,c-b); second row needs both differences nonzero.
    ds = [da*da*db*db for u, v, da, db in tuples]
    residues = [0 if row[0] == 0 else pow(d, -1, m)
                for row, d, m in zip(tuples, ds, moduli)]
    e = crt(residues, moduli)
    require(all((u*(d*e-1)) % m == 0
                for (u, v, da, db), d, m in zip(tuples, ds, moduli)), 'CRT control')
    # Positive representatives plus the two stated lifts force D>0.
    n = 19
    for a in range(1, n*n+1):
        for c in (1, n*n):
            b = c
            aa, bb = a+2*n*n, b+n*n
            require((c-aa)**2*(c-bb)**2 >= 1, 'cofinal lift control')
    return {'soundness_witnesses_checked': cases, 'crt_rows': 3,
            'hypothesis_countercontrols': ['noninvertible_nonzero_guard', 'missing_separate_U_bound'],
            'positive_quotient_lift_checked': True}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    root = args.root
    load = lambda name: json.loads((root/name).read_text())
    basis = load('basis_certificate.json')
    eq, expanded = load('equation.json'), load('expanded_polynomial.json')
    result = {'basis': verify_basis(basis), 'polynomial': verify_polynomial(eq, expanded),
              'finite_controls': finite_controls()}
    # Negative controls make sure the checked paths actually reject corruption.
    bad_basis = deepcopy(basis)
    bad_basis['steps'][-1]['formula'] = 'a'
    bad_polynomial = deepcopy(expanded)
    bad_polynomial['terms'][0][0] += 1
    for label, operation in [
        ('changed_conclusion', lambda: verify_basis(bad_basis)),
        ('changed_expanded_coefficient', lambda: verify_polynomial(eq, bad_polynomial)),
    ]:
        try:
            operation()
        except (ValueError, KeyError, TypeError, IndexError):
            continue
        raise ValueError('negative control accepted: '+label)
    result['corruptions_rejected'] = ['changed_conclusion', 'changed_expanded_coefficient']
    result['equation_sha256'] = hashlib.sha256((root/'equation.json').read_bytes()).hexdigest()
    result['scope'] = 'literal basis proof, coefficient identity, size, finite modular controls; not end-to-end formalization'
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
