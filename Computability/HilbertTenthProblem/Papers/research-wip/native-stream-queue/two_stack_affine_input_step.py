#!/usr/bin/env python3
"""Two positive binary stacks: exact scalar steps and a fixed affine input prefix.

Finite iteration is not supplied by this scalar certificate.
"""
import argparse
from itertools import product
import json
from math import lcm
from pathlib import Path
import random

from residue_affine_ancestor_pumping import Circuit, horner, interpolate
from residue_affine_factored_counter_step import finish

EMPTY = -1
SYMBOLS = (EMPTY, 0, 1)
COLS = ('ns', 'nc', 'rs', 'rc', 'ts', 'tc', 'us', 'uc')


def encode(word):
    return (1 << len(word)) + sum(bit << j for j, bit in enumerate(word))


def decode(number):
    assert number > 0
    return tuple((number >> j) & 1 for j in range(number.bit_length()-1))


def top(number):
    return EMPTY if number == 1 else number % 2


def keep(symbol):
    return () if symbol == EMPTY else (symbol,)


def push(symbol, bit):
    return (bit,)+keep(symbol)


def stack_coefficients(symbol, word):
    value = sum(bit << j for j, bit in enumerate(word))
    scale = 1 << len(word)
    if symbol == EMPTY:
        return 0, 1, 0, scale+value
    return 2, symbol, scale, value


def compile_branches(K, actions):
    assert set(actions) == set(product(range(1, K+1), SYMBOLS, SYMBOLS))
    branches = []
    for (state, left_read, right_read), (target, left_word, right_word) in sorted(actions.items()):
        assert 1 <= target <= K
        d, c, a, b = stack_coefficients(left_read, left_word)
        e, f, g, h = stack_coefficients(right_read, right_word)
        row = dict(ns=K*d, nc=K*(c-1)+state, rs=e, rc=f,
                   ts=K*a, tc=K*(b-1)+target, us=g, uc=h,
                   state=state, target=target, left_read=left_read, right_read=right_read,
                   left_word=left_word, right_word=right_word)
        branches.append(row)
    return branches


def compile_tables(branches):
    rational = {name: interpolate([row[name] for row in branches]) for name in COLS}
    denominator = lcm(*(c.denominator for row in rational.values() for c in row))
    return denominator, {name: [int(denominator*c) for c in row] for name, row in rational.items()}


def source(c, tables, n, r, nt, rt, z, v, P, Q, one=False):
    D, coefficients = tables
    B = len(coefficients['ns'])
    table = {key: horner(c, coefficients[key], z) for key in COLS}
    sides = [(c.add(z, v), B+1)]
    for value, quotient, a, b in ((n, P, 'ns', 'nc'), (r, Q, 'rs', 'rc'),
                                   (nt, P, 'ts', 'tc'), (rt, Q, 'us', 'uc')):
        sides.append((c.mul(D, value), c.add(c.mul(table[a], quotient), table[b])))
    return finish(c, sides, one)


def word_step(K, actions, n, r):
    left, state0 = divmod(n-1, K)
    left, state = left+1, state0+1
    lw, rw = decode(left), decode(r)
    key = (state, lw[0] if lw else EMPTY, rw[0] if rw else EMPTY)
    target, lp, rp = actions[key]
    newleft = encode(tuple(lp)+(lw[1:] if lw else ()))
    newright = encode(tuple(rp)+(rw[1:] if rw else ()))
    return K*(newleft-1)+target, newright


def witness(K, branches, n, r, selected=None, empty_quotient=1):
    left, state0 = divmod(n-1, K)
    left, state = left+1, state0+1
    if selected is None:
        selected = next(j for j, row in enumerate(branches)
                        if (row['state'], row['left_read'], row['right_read']) ==
                        (state, top(left), top(r)))
    P = left//2 if left > 1 else empty_quotient
    Q = r//2 if r > 1 else empty_quotient
    return selected+1, len(branches)-selected, P, Q


def decoder_fixture():
    """Convert raw sentinel x to the ordinary MSB-first binary word for x."""
    K, actions = 2, {}
    for state, left, right in product(range(1, K+1), SYMBOLS, SYMBOLS):
        if state == 2:
            result = 2, keep(left), keep(right)
        elif right == EMPTY:
            result = 2, push(left, 1), ()
        else:
            result = 1, push(left, right), ()
        actions[state, left, right] = result
    return K, actions


def cleanup_fixture():
    K, actions = 2, {}
    for state, left, right in product(range(1, K+1), SYMBOLS, SYMBOLS):
        if state == 2:
            result = 2, keep(left), keep(right)
        else:
            result = (2 if left == right == EMPTY else 1), (), ()
        actions[state, left, right] = result
    return K, actions


def unrolled_source(c, tables, x, scale, offset, middle, locals_, one=False):
    """Duration is the fixed Python list length, not an existential integer."""
    current = (1, c.add(c.mul(scale, x), offset))
    results = []
    targets = list(middle)+[(2, 1)]
    assert len(targets) == len(locals_)
    for target, supplied in zip(targets, locals_):
        results.append(source(c, tables, *current, *target, *supplied, one))
        current = target
    if not one:
        return tuple(value for row in results for value in row)
    value = results[0]
    for following in results[1:]:
        value = c.add(value, following)
    return value


def bounded_history_checks():
    K, actions = cleanup_fixture()
    branches = compile_branches(K, actions)
    tables = compile_tables(branches)
    B, cases, accepted, boundary_errors = len(branches), 0, 0, 0
    for t in range(1, 9):
        for x in range(1, 65):
            current, history, locals_ = (1, x), [], []
            for _ in range(t):
                locals_.append(witness(K, branches, *current))
                current = word_step(K, actions, *current)
                history.append(current)
            reached = current == (2, 1)
            assert reached == (x.bit_length() <= t)
            # The source fixes its last configuration to (2,1), even for
            # deliberately incomplete histories that have not reached it.
            c = Circuit()
            residuals = unrolled_source(c, tables, x, 1, 0, history[:-1], locals_)
            assert (not any(residuals)) == reached
            assert c.counts == {'M':8*B*t+1, 'A':(8*B-3)*t+1}
            assert len(residuals) == 5*t and 2*len(history[:-1])+4*t == 6*t-2
            c = Circuit()
            polynomial = unrolled_source(c, tables, x, 1, 0, history[:-1], locals_, True)
            assert polynomial == sum(r*r for r in residuals)
            assert c.counts == {'M':(8*B+5)*t+1, 'A':(8*B+7)*t}
            if reached:
                assert any(unrolled_source(Circuit(), tables, x+1, 1, 0, history[:-1], locals_))
                boundary_errors += 1
            accepted += reached
            cases += 1
    return dict(fixed_duration_history_cases=cases, reaching_histories=accepted,
                wrong_initial_boundary_cases=boundary_errors,
                graph_operations='2+t*(16B-3)', equations='5t', positive_witnesses='6t-2',
                polynomial_operations='(16B+12)t+1',
                scope='Each t is a fixed finite unrolling; no existential-duration compilation')


def symbolic_check(tables):
    import sympy as sp
    n, r, nt, rt, z, v, P, Q = sp.symbols('n r nt rt z v P Q')
    D, coefficients = tables
    table = {name: sum(c*z**j for j, c in enumerate(row)) for name, row in coefficients.items()}
    expected = [z+v-(len(coefficients['ns'])+1)]
    for value, quotient, a, b in ((n, P, 'ns', 'nc'), (r, Q, 'rs', 'rc'),
                                   (nt, P, 'ts', 'tc'), (rt, Q, 'us', 'uc')):
        expected.append(D*value-table[a]*quotient-table[b])
    actual = source(Circuit(), tables, n, r, nt, rt, z, v, P, Q)
    assert all(sp.expand(a-b) == 0 for a, b in zip(actual, expected))
    polynomial = source(Circuit(), tables, n, r, nt, rt, z, v, P, Q, True)
    assert sp.expand(polynomial-sum(e*e for e in expected)) == 0
    return dict(source_identities=5, sum_of_squares_identity=True)


def scalar_checks(K, actions, branches, tables):
    true = candidates = empty_cases = 0
    B = len(branches)
    D, coefficients = tables
    for j, row in enumerate(branches, 1):
        for name in COLS:
            assert sum(c*j**k for k, c in enumerate(coefficients[name])) == D*row[name]
    for state, left, right in product(range(1, K+1), range(1, 10), range(1, 10)):
        n = K*(left-1)+state
        nt, rt = word_step(K, actions, n, right)
        correct = witness(K, branches, n, right)
        for one in (False, True):
            c = Circuit()
            assert source(c, tables, n, right, nt, rt, *correct, one) == (0 if one else (0,)*5)
            assert c.counts == {'M':8*B+5*one, 'A':8*B-3+9*one}
            true += 1
        for selected in range(B):
            supplied = witness(K, branches, n, right, selected)
            for outleft, outright in {(nt, rt), (nt+1, rt), (nt, rt+1)}:
                value = source(Circuit(), tables, n, right, outleft, outright, *supplied)
                assert (not any(value)) == (selected+1 == correct[0] and (outleft, outright) == (nt, rt))
                candidates += 1
        if left == 1 or right == 1:
            for free in (2, 5, 31):
                supplied = witness(K, branches, n, right, empty_quotient=free)
                assert not any(source(Circuit(), tables, n, right, nt, rt, *supplied))
                empty_cases += 1
    rng = random.Random(21618)
    for _ in range(256):
        values = [rng.randint(1, 100) for _ in range(8)]
        direct = source(Circuit(), tables, *values)
        assert source(Circuit(), tables, *values, True) == sum(x*x for x in direct)
    return dict(genuine_graph_checks=true, independent_branch_output_candidates=candidates,
                free_positive_empty_quotient_cases=empty_cases, arbitrary_polynomial_identities=256,
                symbolic=symbolic_check(tables))


def prefix_and_decoder_checks(K, actions, branches, tables):
    prefixes = decoder_runs = certified_decoder_steps = 0
    for length in range(7):
        for p in product((0, 1), repeat=length):
            scale, offset = 1 << length, sum(bit << j for j, bit in enumerate(p))
            for x in range(1, 129):
                c = Circuit()
                loaded = c.add(c.mul(scale, x), offset)
                assert c.counts == {'M':1, 'A':1}
                assert loaded == encode(p+decode(x))
                prefixes += 1
    for x in range(1, 1025):
        n, r, steps = 1, x, 0
        while (n-1) % K+1 == 1:
            nt, rt = word_step(K, actions, n, r)
            if x <= 128:
                supplied = witness(K, branches, n, r)
                assert not any(source(Circuit(), tables, n, r, nt, rt, *supplied))
                certified_decoder_steps += 1
            n, r, steps = nt, rt, steps+1
            assert steps <= x.bit_length()
        assert r == 1 and steps == x.bit_length()
        left = (n-2)//K+1
        assert decode(left) == tuple(map(int, bin(x)[2:]))
        decoder_runs += 1
    cleanup = 0
    for left, right in product(range(1, 65), repeat=2):
        duration = 0
        while left > 1 or right > 1:
            # Both stacks pop once when nonempty; an empty one stays empty.
            left = left//2 if left > 1 else 1
            right = right//2 if right > 1 else 1
            duration += 1
            assert duration <= 6
        assert left == right == 1
        cleanup += 1
    return dict(prefix_loader_checks=prefixes, literal_affine_loader_operations=2,
                ordinary_input_decoder_runs=decoder_runs,
                certified_decoder_steps=certified_decoder_steps,
                cleanup_pairs=cleanup,
                scope='Explicit decoder and cleanup fixtures; universal interpreter table is not transcribed')


def verify():
    K, actions = decoder_fixture()
    branches = compile_branches(K, actions)
    tables = compile_tables(branches)
    B = len(branches)
    return dict(status='PASS_TWO_STACK_AFFINE_INPUT_STEP',
                generic_graph='16B-3=8B M+(8B-3)A',
                generic_polynomial='16B+11=(8B+5)M+(8B+6)A',
                positive_witnesses=4, equations=5,
                fixture=dict(states=K, branches=B, graph_operations=16*B-3,
                             polynomial_operations=16*B+11,
                             interpolation_denominator=tables[0], coefficient_rows=tables[1],
                             universal=False),
                scalar=scalar_checks(K, actions, branches, tables),
                input=prefix_and_decoder_checks(K, actions, branches, tables),
                bounded_history=bounded_history_checks(),
                established_complete_universal_bound=75,
                limits='Exact scalar graph and fixed affine ordinary-input loader. '
                       'Universal finite iteration and packing remain unpaid; no new complete universal bound.')


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
    print('Four positive step witnesses; affine ordinary-input prefix costs 1M+1A; iteration unpaid.')
