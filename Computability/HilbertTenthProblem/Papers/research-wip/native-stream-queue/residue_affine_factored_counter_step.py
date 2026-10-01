#!/usr/bin/env python3
"""Paid scalar residue graphs and a factored prime-counter transition compiler.

No finite-iteration certificate or unencoded prime-power loader is claimed.
"""
import argparse
from collections import Counter
from itertools import product
import json
from math import gcd, lcm, prod
from pathlib import Path
import random

from residue_affine_ancestor_pumping import Circuit, horner, interpolate, table_polynomials


def finish(c, sides, one):
    if not one:
        return tuple(left-right for left, right in sides)
    residuals = [c.sub(left, right) for left, right in sides]
    squares = [c.mul(r, r) for r in residuals]
    value = squares[0]
    for square in squares[1:]:
        value = c.add(value, square)
    return value


def bounded_residue_source(c, tables, n, y, q, s, v, one=False):
    b, L, P, G = tables
    sides = [(c.add(n, b+1), c.add(c.mul(b, q), s)),
             (c.add(s, v), b+1)]
    pv, gv = horner(c, P, s), horner(c, G, s)
    sides.append((c.mul(L, y), c.add(c.mul(pv, q), gv)))
    return finish(c, sides, one)


def shortcut_source(c, n, y, q, s, v, one=False):
    twice = c.add(q, q)
    sides = [(c.add(n, 3), c.add(twice, s)),
             (c.add(y, 1), c.sub(c.mul(twice, s), q)),
             (c.add(s, v), 3)]
    return finish(c, sides, one)


def counter_branches(K, primes, instructions):
    assert set(instructions) == set(range(1, K+1))
    assert all(gcd(K, p) == 1 for p in primes)
    result = []
    for state, instruction in sorted(instructions.items()):
        kind, register, *targets = instruction
        p = primes[register]
        choices = [(p, 1, targets[0], 'inc')] if kind == 'inc' else [
            (1, p, targets[0], 'dec'), (1, 1, targets[1], 'zero')]
        for A, D, target, branch_kind in choices:
            assert 1 <= target <= K
            E = A*(K-state)-D*(K-target)
            result.append(dict(I=state, A=A, D=D, E=E, p=p,
                               target=target, kind=branch_kind))
    return result


def compile_tables(branches):
    rational = {name: interpolate([b[name] for b in branches])
                for name in ('I', 'A', 'D', 'E', 'p')}
    L = lcm(*(coefficient.denominator for row in rational.values() for coefficient in row))
    return L, {name: [int(L*c) for c in row] for name, row in rational.items()}


def counter_source(c, K, tables, n, y, z, v, P, Q, U, V, one=False):
    L, rows = tables
    B = len(rows['I'])
    I, A, D, E, p = [horner(c, rows[name], z) for name in ('I', 'A', 'D', 'E', 'p')]
    sides = [(c.add(z, v), B+1),
             (c.add(c.mul(L, n), L*K), c.add(c.mul(L*K, P), I)),
             (c.mul(D, y), c.add(c.mul(A, n), E))]
    AD = c.add(A, D)
    h = c.sub(c.add(p, L), AD)
    guard = c.add(c.mul(h, P), c.sub(c.add(AD, p), 2*L))
    sides += [(guard, c.add(c.mul(p, Q), U)), (c.add(U, V), p)]
    return finish(c, sides, one)


def scalar_counter_step(K, primes, instructions, n):
    P, state0 = divmod(n-1, K)
    P, state = P+1, state0+1
    kind, register, *targets = instructions[state]
    p = primes[register]
    if kind == 'inc':
        P, state = p*P, targets[0]
    elif P % p == 0:
        P, state = P//p, targets[0]
    else:
        state = targets[1]
    return K*(P-1)+state


def witnesses(K, tables, branches, n, branch=None):
    L, _ = tables
    payload, state0 = divmod(n-1, K)
    P, state = payload+1, state0+1
    if branch is None:
        branch = next(j for j, b in enumerate(branches)
                      if b['I'] == state and (b['kind'] == 'inc' or
                      (P % b['p'] == 0) == (b['kind'] == 'dec')))
    b = branches[branch]
    h = b['p']+1-b['A']-b['D']
    Z = h*P+b['A']+b['D']-2
    quotient, remainder = divmod(Z, b['p'])
    # Deliberately supply a positive but false remainder on invalid zero branches.
    remainder = remainder or 1
    return (branch+1, len(branches)-branch, P, quotient+1,
            L*remainder, L*(b['p']-remainder))


def fixture():
    K, primes = 11, (2, 3, 5)
    instructions = {1: ('dec', 0, 2, 3), 2: ('inc', 1, 1),
                    3: ('dec', 1, 4, 5), 4: ('inc', 2, 3),
                    5: ('dec', 2, 5, 6), 6: ('inc', 0, 6)}
    instructions.update({j: ('inc', 0, j) for j in range(7, K+1)})
    return K, primes, instructions


def check_residue_slack():
    generated = wrong = 0
    for b in (2, 3, 4, 6, 9):
        slopes = [1] + [1+r*(b+1) for r in range(1, b)]
        offsets = [0]+[r+2 for r in range(1, b)]
        tables = (b, *table_polynomials(slopes, offsets))
        for n in range(1, 101):
            y = slopes[n % b]*(n//b)+offsets[n % b]
            q, s, v = n//b+1, n % b+1, b-n % b
            for one in (False, True):
                c = Circuit()
                value = bounded_residue_source(c, tables, n, y, q, s, v, one)
                assert value == (0 if one else (0, 0, 0))
                assert c.counts == {'M':2*b+1+3*one, 'A':2*b+2+5*one}
                generated += 1
        for n in range(1, 16):
            expected = slopes[n % b]*(n//b)+offsets[n % b]
            for q, s, v in product(range(1, 6), range(1, b+2), range(1, b+2)):
                for y in (max(1, expected-1), expected, expected+1):
                    result = bounded_residue_source(Circuit(), tables, n, y, q, s, v)
                    valid = (q == n//b+1 and s == n % b+1 and v == b-n % b and y == expected)
                    assert (not any(result)) == valid
                    wrong += 1
    for n in range(1, 1001):
        y = n//2 if n % 2 == 0 else (3*n+1)//2
        q, s, v = n//2+1, n % 2+1, 2-n % 2
        for one in (False, True):
            c = Circuit()
            assert shortcut_source(c, n, y, q, s, v, one) == (0 if one else (0, 0, 0))
            assert c.counts == {'M':1+3*one, 'A':6+5*one}
    return dict(generated_generic_checks=generated, independently_supplied_candidates=wrong,
                shortcut_checks=2000, generic_graph='4b+3=(2b+1)M+(2b+2)A',
                generic_polynomial='4b+11=(2b+4)M+(2b+7)A',
                shortcut_graph='7=1M+6A', shortcut_polynomial='15=4M+11A',
                positive_witnesses=3)


def symbolic_source(K, tables):
    import sympy as sp
    names = 'n y z v P Q U V'
    n, y, z, v, P, Q, U, V = sp.symbols(names)
    L, rows = tables
    values = {key: sum(coefficient*z**j for j, coefficient in enumerate(row))
              for key, row in rows.items()}
    I, A, D, E, p = [values[key] for key in ('I', 'A', 'D', 'E', 'p')]
    expected = (z+v-(len(rows['I'])+1), L*n+L*K-L*K*P-I,
                D*y-A*n-E, (p+L-A-D)*P+A+D+p-2*L-p*Q-U, U+V-p)
    actual = counter_source(Circuit(), K, tables, n, y, z, v, P, Q, U, V)
    assert all(sp.expand(a-b) == 0 for a, b in zip(actual, expected))
    polynomial = counter_source(Circuit(), K, tables, n, y, z, v, P, Q, U, V, True)
    assert sp.expand(polynomial-sum(e*e for e in expected)) == 0
    return dict(equation_identities=5, sum_of_squares_identity=True)


def check_counter():
    K, primes, instructions = fixture()
    branches = counter_branches(K, primes, instructions)
    tables = compile_tables(branches)
    L, rows = tables
    B = len(branches)
    for j, branch in enumerate(branches, 1):
        for key in rows:
            assert sum(coefficient*j**i for i, coefficient in enumerate(rows[key])) == L*branch[key]
    true = candidates = perturbations = 0
    for n in range(1, 661):
        y = scalar_counter_step(K, primes, instructions, n)
        witness = witnesses(K, tables, branches, n)
        assert min(witness) > 0
        for one in (False, True):
            c = Circuit()
            assert counter_source(c, K, tables, n, y, *witness, one) == (0 if one else (0,)*5)
            assert c.counts == {'M':5*B+1+5*one, 'A':5*B+7+9*one}
            true += 1
        for j in range(B):
            proposed = witnesses(K, tables, branches, n, j)
            for out in {max(1, y-1), y, y+1}:
                result = counter_source(Circuit(), K, tables, n, out, *proposed)
                assert (not any(result)) == (j+1 == witness[0] and out == y)
                candidates += 1
        for coordinate in range(6):
            changed = list(witness)
            changed[coordinate] += 1
            assert any(counter_source(Circuit(), K, tables, n, y, *changed))
            perturbations += 1
    # Independent register-vector execution, rather than numerical divisibility.
    traces = steps = 0
    for original in product(range(4), repeat=3):
        registers, state = list(original), 1
        n = K*(prod(p**r for p, r in zip(primes, registers))-1)+state
        while state != 6:
            kind, register, *targets = instructions[state]
            if kind == 'inc':
                registers[register] += 1
                state = targets[0]
            elif registers[register]:
                registers[register] -= 1
                state = targets[0]
            else:
                state = targets[1]
            n = scalar_counter_step(K, primes, instructions, n)
            assert n == K*(prod(p**r for p, r in zip(primes, registers))-1)+state
            steps += 1
            assert steps < 10000
        assert n == 6 and not any(registers)
        traces += 1
    # Every full residue class really has one rational affine update.
    modulus = K*prod(primes)
    affine = 0
    for r in range(modulus):
        start = r or modulus
        y0 = scalar_counter_step(K, primes, instructions, start)
        slope = scalar_counter_step(K, primes, instructions, start+modulus)-y0
        assert slope > 0 and gcd(slope, modulus) > 1
        for j in range(2, 6):
            assert scalar_counter_step(K, primes, instructions, start+j*modulus) == y0+j*slope
            affine += 1
    return dict(symbolic=symbolic_source(K, tables), K=K, register_primes=primes,
                branches=B, interpolation_denominator=L, coefficient_rows=rows,
                graph_operations=10*B+8, graph_M=5*B+1, graph_A=5*B+7,
                polynomial_operations=10*B+22, polynomial_M=5*B+6, polynomial_A=5*B+16,
                positive_witnesses=6, equations=5,
                full_residue_modulus=modulus, unfactored_slack_graph_operations=4*modulus+3,
                true_source_checks=true, independent_branch_output_candidates=candidates,
                positive_coordinate_perturbations=perturbations, register_traces=traces,
                register_steps=steps, affine_class_comparisons=affine,
                fixture_is_universal=False)


def check_nonunit_escape():
    comparisons = 0
    for h in range(3, 11):
        target = 2**h-1
        expected = {2**j-1 for j in range(1, h)}
        actual = set()
        for x in range(1, 2**h):
            n = 2*x+1
            while n < target:
                assert n % 2 == 1
                n = 2*n+1
            if n == target:
                actual.add(x)
            comparisons += 1
        assert actual == expected and len(actual) == h-1
    return dict(exact_monotone_trajectory_checks=comparisons,
                map='f(2q)=q, f(2q+1)=4q+3', loader='2x+1',
                target='2^h-1', exact_finite_language='{2^j-1:1<=j<h}',
                maximum_checked_finite_cardinality=9,
                scope='A counterexample to extending the unit-slope finite bound; not universal')


def verify():
    return dict(status='PASS_RESIDUE_AFFINE_FACTORED_COUNTER_STEP',
                residue_slack=check_residue_slack(), counter=check_counter(),
                nonunit_escape=check_nonunit_escape(),
                limits='Complete positive one-step graphs only. Prime-power loading, synchronized '
                       'finite histories, acceptance endpoint and universal iteration remain unpaid.',
                established_complete_universal_bound=75)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'])
    print('Generic graph 4b+3; shortcut 7; factored counter graph 10B+8; iteration unpaid.')
