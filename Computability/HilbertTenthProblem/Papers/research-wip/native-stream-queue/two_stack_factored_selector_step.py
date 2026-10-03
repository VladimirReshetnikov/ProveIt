"""Factor the known source-state/read columns of a positive two-stack step.

The four arbitrary output columns remain interpolated. This is an exact
scalar graph and fixed-duration family, not a variable-duration compiler.
"""
import argparse
from itertools import product
import json
from math import comb
from pathlib import Path
import random

import sympy as sp

import two_stack_affine_input_step as prior

Circuit = prior.Circuit
OUTPUT_COLUMNS = ('ts', 'tc', 'us', 'uc')


def tables_for(branches):
    denominator, old = prior.compile_tables(branches)
    # Old branch nodes1,...,B become13,...,B+12. Substitution happens
    # entirely in the fixed coefficient compiler, not in the paid DAG.
    shifted = {}
    for name in OUTPUT_COLUMNS:
        coefficients = old[name]
        shifted[name] = [sum(coefficients[k]*comb(k, j)*(-12)**(k-j)
                             for k in range(j, len(coefficients)))
                         for j in range(len(coefficients))]
    return denominator, shifted


def source(c, K, tables, n, r, nt, rt, j, jbar, left, leftbar,
           right, rightbar, P, Q, one=False):
    denominator, coefficients = tables
    sides = [(c.add(j, jbar), K+1),
             (c.add(left, leftbar), 4),
             (c.add(right, rightbar), 4)]
    lm = c.sub(left, 2)
    lc = c.mul(lm, lm)
    ld = c.sub(left, lc)
    actual_left = c.add(c.mul(ld, P), lc)
    sides.append((c.add(n, K), c.add(c.mul(K, actual_left), j)))
    rm = c.sub(right, 2)
    rc = c.mul(rm, rm)
    rd = c.sub(right, rc)
    sides.append((r, c.add(c.mul(rd, Q), rc)))
    index = c.add(c.add(c.mul(9, j), c.mul(3, left)), right)
    output = {name: prior.horner(c, coefficients[name], index)
              for name in OUTPUT_COLUMNS}
    sides.extend(((c.mul(denominator, nt),
                   c.add(c.mul(output['ts'], P), output['tc'])),
                  (c.mul(denominator, rt),
                   c.add(c.mul(output['us'], Q), output['uc']))))
    return prior.finish(c, sides, one)


def witness(K, n, r, empty_quotient=1):
    quotient, residue = divmod(n-1, K)
    X, j = quotient+1, residue+1
    left = prior.top(X)+2
    right = prior.top(r)+2
    P = X//2 if X > 1 else empty_quotient
    Q = r//2 if r > 1 else empty_quotient
    return j, K+1-j, left, 4-left, right, 4-right, P, Q


def unrolled_source(c, K, tables, x, scale, offset, start, halt,
                    configurations, local_witnesses, one=False):
    n, r = start, c.add(c.mul(scale, x), offset)
    result = []
    for index, supplied in enumerate(local_witnesses):
        nt, rt = configurations[index] if index < len(local_witnesses)-1 else (halt, 1)
        result.append(source(c, K, tables, n, r, nt, rt, *supplied, one))
        n, r = nt, rt
    if one:
        output = result[0]
        for term in result[1:]:
            output = c.add(output, term)
        return output
    return tuple(value for step in result for value in step)


def verify_symbolic(K, tables):
    n, r, nt, rt, j, jb, l, lb, rr, rb, P, Q = sp.symbols('n r nt rt j jb l lb rr rb P Q')
    args = (n, r, nt, rt, j, jb, l, lb, rr, rb, P, Q)
    denominator, coefficients = tables
    index = 9*j+3*l+rr
    values = {name: sum(a*index**k for k, a in enumerate(row))
              for name, row in coefficients.items()}
    lc, rc = (l-2)**2, (rr-2)**2
    expected = [j+jb-K-1, l+lb-4, rr+rb-4,
                n+K-K*((l-lc)*P+lc)-j,
                r-(rr-rc)*Q-rc,
                denominator*nt-values['ts']*P-values['tc'],
                denominator*rt-values['us']*Q-values['uc']]
    actual = source(Circuit(), K, tables, *args)
    assert all(sp.expand(a-b) == 0 for a, b in zip(actual, expected))
    # Keep polynomial composition factored to avoid an irrelevant expansion.
    actual_poly = source(Circuit(), K, tables, *args, True)
    assert sp.expand(actual_poly-sum(term*term for term in actual)) == 0
    return dict(exact_residual_identities=7, exact_sum_of_squares_identity=True)


def verify_scalar():
    K, actions = prior.decoder_fixture()
    branches = prior.compile_branches(K, actions)
    tables = tables_for(branches)
    denominator, coefficients = tables
    B = len(branches)
    for old_index, row in enumerate(branches, 1):
        j, left, right = row['state'], row['left_read']+2, row['right_read']+2
        new_index = 9*j+3*left+right
        assert new_index == old_index+12
        for name in OUTPUT_COLUMNS:
            assert sum(a*new_index**k for k, a in enumerate(coefficients[name])) == denominator*row[name]
    accepted = wrong = free_empty = 0
    for j, X, r in product(range(1, K+1), range(1, 13), range(1, 13)):
        n = K*(X-1)+j
        nt, rt = prior.word_step(K, actions, n, r)
        supplied = witness(K, n, r)
        for one in (False, True):
            c = Circuit()
            actual = source(c, K, tables, n, r, nt, rt, *supplied, one)
            assert actual == (0 if one else (0,)*7)
            assert c.counts == {'M':4*B+7+7*one, 'A':4*B+11+13*one}
            accepted += 1
        for candidate_j, l, rr in product(range(1, K+1), range(1, 4), range(1, 4)):
            guessed = (candidate_j, K+1-candidate_j, l, 4-l, rr, 4-rr, supplied[-2], supplied[-1])
            for out in ((nt, rt), (nt+1, rt), (nt, rt+1)):
                actual = source(Circuit(), K, tables, n, r, *out, *guessed)
                assert (not any(actual)) == (guessed == supplied and out == (nt, rt))
                wrong += 1
        if X == 1 or r == 1:
            for free in (2, 7, 31):
                assert not any(source(Circuit(), K, tables, n, r, nt, rt,
                                      *witness(K, n, r, free)))
                free_empty += 1
    rng = random.Random(8018)
    for _ in range(128):
        args = [rng.randint(1, 20) for _ in range(12)]
        residuals = source(Circuit(), K, tables, *args)
        assert source(Circuit(), K, tables, *args, True) == sum(v*v for v in residuals)
    return dict(states=K, branches=B, graph_operations=8*B+18,
                polynomial_operations=8*B+38, genuine_checks=accepted,
                selector_and_output_checks=wrong, arbitrary_empty_quotient_checks=free_empty,
                arbitrary_polynomial_identities=128, symbolic=verify_symbolic(K, tables),
                fixed_denominator=denominator, output_coefficients=coefficients,
                universal_fixture=False)


def verify_histories():
    K, actions = prior.cleanup_fixture()
    branches = prior.compile_branches(K, actions)
    tables, B = tables_for(branches), len(branches)
    cases = accepting = 0
    for t in range(1, 9):
        for x in range(1, 65):
            current, states, local = (1, x), [], []
            for _ in range(t):
                local.append(witness(K, *current))
                current = prior.word_step(K, actions, *current)
                states.append(current)
            reached = current == (2, 1)
            assert reached == (x.bit_length() <= t)
            c = Circuit()
            residuals = unrolled_source(c, K, tables, x, 1, 0, 1, 2, states[:-1], local)
            assert (not any(residuals)) == reached
            assert c.counts == {'M':(4*B+7)*t+1, 'A':(4*B+11)*t+1}
            assert len(residuals) == 7*t and 2*(t-1)+8*t == 10*t-2
            c = Circuit()
            polynomial = unrolled_source(c, K, tables, x, 1, 0, 1, 2, states[:-1], local, True)
            assert polynomial == sum(r*r for r in residuals)
            assert c.counts == {'M':(4*B+14)*t+1, 'A':(4*B+25)*t}
            cases += 1
            accepting += reached
    return dict(cases=cases, accepting=accepting,
                graph_operations='2+t*(8B+18)', equations='7t', positive_witnesses='10t-2',
                polynomial_operations='(8B+39)t+1',
                scope='A separate finite unrolling for each fixed t; no variable-duration certificate')


def verify():
    return dict(status='PASS_TWO_STACK_FACTORED_SELECTOR_STEP',
                graph=dict(operations='8B+18', multiplications='4B+7', additions='4B+11',
                           positive_witnesses=8, equations=7),
                polynomial=dict(operations='8B+38', multiplications='4B+14', additions='4B+24'),
                scalar=verify_scalar(), histories=verify_histories(),
                preserved='Same generic total deterministic two-stack tables and affine ordinary-input loader',
                limits='More local witnesses and comparisons than the prior16B-3 graph. '
                       'Arbitrary-duration packing remains unpaid; no new complete universal bound.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(receipt.read_text()) == result, 'receipt mismatch'
    print(result['status'], result['graph'], result['polynomial'])
