"""Faithful free-group embeddings and5/6/7-operation input curves.

Matrices are flat row-major four-tuples. This is only the input-loader
component; it does not encode subgroup membership or prove universality.
"""
import argparse
from collections import Counter
from fractions import Fraction
import json
from pathlib import Path
import random

import sympy as sp


IDENTITY = (1, 0, 0, 1)
U = (1, 4, 0, 1)
B = (1, 0, 1, 1)
A = (5, -16, 1, -3)
SCHEDULE = (
    ('t', '*', 8, 'x'),
    ('q', '*', 't', 't'),
    ('v', '*', 'q', 'q'),
    ('h', '-', 'q', 't'),
    ('two_q', '+', 'q', 'q'),
    ('p_inner', '-', 'two_q', 1),
    ('p', '*', 't', 'p_inner'),
    ('ell', '+', 'p', 'h'),
    ('two_p', '+', 'p', 'p'),
    ('r_inner', '+', 'two_p', 'ell'),
    ('r', '*', 4, 'r_inner'),
    ('w11', '+', 1, 'r'),
    ('w12', '*', -64, 'p'),
    ('two_ell', '+', 'ell', 'ell'),
    ('three_v', '*', 3, 'v'),
    ('w21', '-', 'two_ell', 'three_v'),
    ('sixteen_v', '*', 16, 'v'),
    ('last', '-', 'sixteen_v', 'r'),
    ('w22', '+', 1, 'last'),
)
OUTPUTS = ('w11', 'w12', 'w21', 'w22')


def multiply(left, right):
    a, b, c, d = left
    e, f, g, h = right
    return (a*e+b*g, a*f+b*h, c*e+d*g, c*f+d*h)


def determinant(matrix):
    a, b, c, d = matrix
    return a*d-b*c


def inverse(matrix):
    a, b, c, d = matrix
    assert determinant(matrix) == 1
    return (d, -b, -c, a)


def matrix_power(matrix, exponent):
    if exponent < 0:
        matrix, exponent = inverse(matrix), -exponent
    answer = IDENTITY
    while exponent:
        if exponent & 1:
            answer = multiply(answer, matrix)
        matrix = multiply(matrix, matrix)
        exponent //= 2
    return answer


def generator(index):
    """Image of a designated basis generator; b has index0 and a index1."""
    return (1+4*index, -16*index*index, 1, 1-4*index)


def execute(x):
    env = {'x': x}
    for name, op, left, right in SCHEDULE:
        a = left if isinstance(left, int) else env[left]
        b = right if isinstance(right, int) else env[right]
        env[name] = a+b if op == '+' else a-b if op == '-' else a*b
    return env


def evaluate_loader(x):
    env = execute(x)
    return tuple(env[name] for name in OUTPUTS)


def commutator(left, right):
    """[g,h]=g h g^-1 h^-1."""
    return multiply(multiply(multiply(left, right), inverse(left)), inverse(right))


def commutator_at_input(x):
    conjugate = multiply(multiply(matrix_power(B, -x), A), matrix_power(B, x))
    return commutator(conjugate, A)


def verify_commutator_loader():
    available = {'x'}
    for name, op, left, right in SCHEDULE:
        assert name not in available and op in ('+', '-', '*')
        assert all(isinstance(item, int) or item in available for item in (left, right))
        available.add(name)
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in SCHEDULE)
    assert len(SCHEDULE) == 19 and counts == {'M': 8, 'A': 11}
    assert multiply(multiply(U, B), inverse(U)) == A == generator(1)
    assert generator(0) == B
    x = sp.Symbol('x')
    env = execute(x)
    actual = tuple(sp.expand(env[name]) for name in OUTPUTS)
    lower_plus, lower_minus = (1, 0, x, 1), (1, 0, -x, 1)
    X = multiply(multiply(lower_minus, A), lower_plus)
    assert sp.expand(determinant(X)-1) == 0
    # Symbolic inverse here is the adjugate, justified by determinant1 above.
    Xinv = (X[3], -X[1], -X[2], X[0])
    direct = multiply(multiply(multiply(X, A), Xinv), inverse(A))
    assert all(sp.expand(a-b) == 0 for a, b in zip(actual, direct))
    assert sp.expand(determinant(actual)-1) == 0
    assert sp.expand(actual[0]+actual[3]-2-65536*x**4) == 0
    degrees = [sp.Poly(value, x).degree() for value in actual]
    assert degrees == [3, 3, 4, 4]
    leading = [sp.Poly(value, x).LC() for value in actual]
    assert leading == [12288, -65536, -12288, 65536]
    cases = list(range(-128, 129))
    rng = random.Random(190419)
    cases += [rng.randint(-10**6, 10**6) for _ in range(128)]
    for value in cases:
        matrix = evaluate_loader(value)
        assert matrix == commutator_at_input(value)
        assert determinant(matrix) == 1
        assert (matrix == IDENTITY) == (value == 0)
    return dict(operations=19, multiplications=8, additions_subtractions=11,
                input='ordinary integer x; intended language domain x>0',
                supplied_witnesses=0, fixed_generators=dict(U=U, B=B, A=A),
                commutator_convention='[g,h]=g h g^-1 h^-1',
                input_word='[b^-x a b^x,a]', schedule=SCHEDULE, outputs=OUTPUTS,
                coordinate_polynomials=[str(value) for value in actual],
                coordinate_degrees=degrees, coordinate_leading_coefficients=[int(v) for v in leading],
                trace_polynomial='2+65536*x^4', determinant_identity=True,
                symbolic_commutator_identity=True, direct_integer_matrix_cases=len(cases),
                fixed_integer_numeral_products_charged=True,
                nonnegative_numerals_only_variant=dict(operations=20, multiplications=8,
                                                       additions_subtractions=12,
                                                       change='replace -64*p by positive12=64*p; w12=0-positive12'))


def verify_embedding():
    for i in range(-32, 33):
        matrix = generator(i)
        assert determinant(matrix) == 1 and matrix[0]+matrix[3] == 2
        assert matrix == multiply(multiply(matrix_power(U, i), B), matrix_power(U, -i))
    records = []
    for rank, depth in ((2, 8), (3, 6), (4, 5)):
        positives = {i+1: generator(i) for i in range(rank)}
        images = {**positives, **{-i: inverse(g) for i, g in positives.items()}}
        frontier = [(IDENTITY, 0)]
        seen = {IDENTITY}
        per_length = []
        for length in range(1, depth+1):
            following = []
            for matrix, last in frontier:
                for letter, image in images.items():
                    if letter == -last:
                        continue
                    candidate = multiply(matrix, image)
                    assert candidate not in seen
                    seen.add(candidate)
                    following.append((candidate, letter))
            expected = 2*rank*(2*rank-1)**(length-1)
            assert len(following) == expected
            per_length.append(expected)
            frontier = following
        records.append(dict(rank=rank, maximum_reduced_word_length=depth,
                            nonempty_distinct_reduced_words=len(seen)-1,
                            per_length=per_length))
    # Exact rational samples of the two strict ping-pong inclusions.
    finite = {Fraction(n, d) for d in range(1, 9) for n in range(-40, 41)}
    outside = [z for z in finite if abs(z) > 2]
    inside = [z for z in finite if abs(z) < 2]
    checks = 0
    for n in range(-8, 9):
        if not n:
            continue
        for z in inside:
            assert abs(z+4*n) > 2
            checks += 1
        for z in outside:
            assert n*z+1 != 0 and abs(z/(n*z+1)) < 2
            checks += 1
        assert abs(Fraction(1, n)) < 2  # V^n acting on infinity.
        checks += 1
    return dict(conjugate_generator_formula_checks=65,
                generator_formula='g_i=[[1+4i,-16i^2],[1,1-4i]]',
                distinguished_generators='b=g_0, a=g_1; other basis generators use distinct indices>=2',
                reduced_word_fixtures=records, rational_ping_pong_checks=checks,
                proof_scope='The note proves freeness for every finite set of distinct integer indices; bounded tests are supporting audits only')


LOADER5 = (
    ('q', '*', 'c', 'x'),
    ('product', '*', 'q', 'x'),
    ('lower', '-', 0, 'product'),
    ('upper_left', '+', 1, 'q'),
    ('lower_right', '-', 1, 'q'),
)
LOADER5_OUTPUTS = ('upper_left', 'c', 'lower', 'lower_right')
LOADER6 = (
    ('four_x', '*', 4, 'x'),
    ('t', '-', 'four_x', 1),
    ('square', '*', 't', 't'),
    ('four_t', '*', 4, 't'),
    ('upper_left', '-', 1, 'four_t'),
    ('lower_right', '+', 1, 'four_t'),
)
LOADER6_OUTPUTS = ('upper_left', -16, 'square', 'lower_right')


def execute_schedule(schedule, inputs, outputs):
    env = dict(inputs)
    for name, op, left, right in schedule:
        a = left if isinstance(left, int) else env[left]
        b = right if isinstance(right, int) else env[right]
        env[name] = a+b if op == '+' else a-b if op == '-' else a*b
    return tuple(name if isinstance(name, int) else env[name] for name in outputs)


def loader5(x, k):
    """k>=1 is a fixed presentation parameter, never an extra runtime input."""
    assert isinstance(k, int) and k >= 1
    return execute_schedule(LOADER5, {'x': x, 'c': 4*k}, LOADER5_OUTPUTS)


def loader6(x):
    return execute_schedule(LOADER6, {'x': x}, LOADER6_OUTPUTS)


def paired_diagonal_target(x, k=None):
    matrix = loader6(x) if k is None else loader5(x, k)
    return (matrix, matrix)


def schreier_generators(k):
    assert isinstance(k, int) and k >= 1
    return [(1, 4*k, 0, 1)]+[generator(i) for i in range(k)]


def verify_quadratic_loaders():
    x, c = sp.symbols('x c')
    reports = {}
    for label, schedule, outputs, inputs, fixed_A, cost in (
        ('fixed_rank5', LOADER5, LOADER5_OUTPUTS,
         {'x': x, 'c': c}, (1, c, 0, 1), 5),
        ('rank_uniform6', LOADER6, LOADER6_OUTPUTS, {'x': x}, A, 6)):
        available = set(inputs)
        for name, op, left, right in schedule:
            assert name not in available and op in ('+', '-', '*')
            assert all(isinstance(v, int) or v in available for v in (left, right))
            available.add(name)
        counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in schedule)
        multiplications = 2 if cost == 5 else 3
        assert len(schedule) == cost and counts == {'M': multiplications, 'A': cost-multiplications}
        actual = tuple(sp.expand(v) for v in execute_schedule(schedule, inputs, outputs))
        target = multiply(multiply((1, 0, -x, 1), fixed_A), (1, 0, x, 1))
        assert all(sp.expand(a-b) == 0 for a, b in zip(actual, target))
        assert sp.expand(determinant(actual)-1) == 0
        assert sp.expand(actual[0]+actual[3]-2) == 0
        degrees = [sp.Poly(v, x).degree() for v in actual]
        assert degrees == [1, 0, 2, 1]
        samples = 0
        for k in ((1, 2, 3, 7, 19) if cost == 5 else (None,)):
            for value in range(-128, 129):
                matrix = loader6(value) if k is None else loader5(value, k)
                fixed = A if k is None else (1, 4*k, 0, 1)
                direct = multiply(multiply(matrix_power(B, -value), fixed), matrix_power(B, value))
                assert matrix == direct and determinant(matrix) == 1
                assert paired_diagonal_target(value, k) == (matrix, matrix)
                samples += 1
        reports[label] = dict(operations=cost, multiplications=multiplications, additions_subtractions=cost-multiplications,
                              supplied_witnesses=0, input='ordinary integer x; intended language domain x>0',
                              fixed_parameter='c=4k, k=N-1>=1 is fixed' if cost == 5 else 'A and B independent of rank',
                              schedule=schedule, outputs=outputs,
                              coordinate_polynomials=[str(v) for v in actual],
                              coordinate_degrees=degrees, determinant_identity=True, trace=2,
                              symbolic_conjugation_identity=True, direct_integer_matrix_cases=samples,
                              repeated_pair_target_has_no_additional_arithmetic=True,
                              fixed_numeral_products_charged=True,
                              fixed_signed_numerals_allowed=True,
                              arithmetic_gates_use_only_nonnegative_literals=True)
    return reports


LOADER7 = (('program_product', '*', 'kappa', 'x'),
           ('loaded_input', '+', 'program_product', 'offset'))+tuple(
    (name, op, 'loaded_input' if left == 'x' else left,
     'loaded_input' if right == 'x' else right)
    for name, op, left, right in LOADER5)


def loader7(x, kappa, offset):
    """The fixed rank-four curve at kappa*x+offset; coefficients are fixed."""
    assert isinstance(kappa, int) and kappa > 0
    assert isinstance(offset, int) and offset > 0
    return execute_schedule(LOADER7, {'x': x, 'c': 12, 'kappa': kappa, 'offset': offset},
                            LOADER5_OUTPUTS)


def verify_affine_loader7():
    x, kappa, offset = sp.symbols('x kappa offset')
    inputs = {'x': x, 'c': 12, 'kappa': kappa, 'offset': offset}
    available = set(inputs)
    for name, op, left, right in LOADER7:
        assert name not in available
        assert all(isinstance(v, int) or v in available for v in (left, right))
        available.add(name)
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in LOADER7)
    assert len(LOADER7) == 7 and counts == {'M': 3, 'A': 4}
    actual = tuple(sp.expand(v) for v in execute_schedule(LOADER7, inputs, LOADER5_OUTPUTS))
    loaded = kappa*x+offset
    expected = (1+12*loaded, 12, -12*loaded*loaded, 1-12*loaded)
    assert all(sp.expand(a-b) == 0 for a, b in zip(actual, expected))
    assert sp.expand(determinant(actual)-1) == 0
    degrees = [sp.Poly(v, x).degree() for v in actual]
    assert degrees == [1, 0, 2, 1]
    A4 = (1, 12, 0, 1)
    cases = 0
    for program in range(13):
        offset, kappa = 2**program, 2**(program+1)
        for value in range(1, 65):
            y = kappa*value+offset
            assert y == 2**program*(2*value+1)
            remainder, valuation = y, 0
            while remainder % 2 == 0:
                valuation += 1
                remainder //= 2
            assert valuation == program and (remainder-1)//2 == value
            direct = multiply(multiply(matrix_power(B, -y), A4), matrix_power(B, y))
            assert loader7(value, kappa, offset) == loader5(y, 3) == direct
            cases += 1
    return dict(operations=7, multiplications=3, additions_subtractions=4,
                supplied_witnesses=0, input='ordinary positive integer x',
                fixed_parameters='kappa=2^(p+1), offset=2^p for fixed program p; c=12',
                schedule=LOADER7, outputs=LOADER5_OUTPUTS,
                coordinate_polynomials=[str(v) for v in actual], coordinate_degrees=degrees,
                determinant_identity=True, symbolic_affine_composition_identity=True,
                integer_matrix_and_unique_valuation_cases=cases,
                no_runtime_exponentiation=True,
                arithmetic_gates_use_only_nonnegative_literals=True,
                scope='Paid affine input composition only; the companion group theorem supplies the single subgroup for the universal coded c.e. set')


def verify_schreier_embedding():
    records = []
    for k, depth in ((1, 8), (2, 6), (3, 5)):
        positives = {i+1: matrix for i, matrix in enumerate(schreier_generators(k))}
        rank = k+1
        assert len(positives) == rank
        assert positives[1] == matrix_power(U, k) and positives[2] == B
        images = {**positives, **{-i: inverse(g) for i, g in positives.items()}}
        seen = {IDENTITY}
        frontier = [(IDENTITY, 0)]
        for length in range(1, depth+1):
            following = []
            for matrix, last in frontier:
                for letter, image in images.items():
                    if letter == -last:
                        continue
                    candidate = multiply(matrix, image)
                    assert candidate not in seen
                    seen.add(candidate)
                    following.append((candidate, letter))
            assert len(following) == 2*rank*(2*rank-1)**(length-1)
            frontier = following
        records.append(dict(k=k, rank=rank, maximum_reduced_word_length=depth,
                            nonempty_distinct_reduced_words=len(seen)-1))
    return dict(basis='a=U^k, b=V, remaining U^i V U^-i for1<=i<k',
                rank='N=k+1', fixed_curve_parameter='c=4k', reduced_word_fixtures=records,
                proof_scope='The note proves freeness using the k-cycle covering graph and its spanning tree, for every fixed k>=1')


LOADER5_SWAPPED = (
    ('q', '*', 'c', 'x'),
    ('square', '*', 'q', 'q'),
    ('lower', '-', 0, 'square'),
    ('upper_left', '+', 1, 'q'),
    ('lower_right', '-', 1, 'q'),
)
SWAPPED_OUTPUTS = ('upper_left', 1, 'lower', 'lower_right')
LOADER6_PROGRAM = (
    ('program_product', '*', 'scaled_kappa', 'x'),
    ('q', '+', 'program_product', 'scaled_offset'),
    ('square', '*', 'q', 'q'),
    ('lower', '-', 0, 'square'),
    ('upper_left', '+', 1, 'q'),
    ('lower_right', '-', 1, 'q'),
)


def swap_conjugate(matrix):
    """Conjugation by S=[[0,1],[1,0]], which is its own inverse."""
    a, b, c, d = matrix
    return (d, c, b, a)


def swapped_schreier_generators(k):
    old = [swap_conjugate(g) for g in schreier_generators(k)]
    return [old[1], old[0]]+old[2:]


def loader5_swapped(x, k):
    assert isinstance(k, int) and k >= 1
    return execute_schedule(LOADER5_SWAPPED, {'x': x, 'c': 4*k}, SWAPPED_OUTPUTS)


def loader6_program(x, scaled_kappa, scaled_offset):
    """Fixed rank-four program coefficients are12*2^(p+1) and12*2^p."""
    assert isinstance(scaled_kappa, int) and scaled_kappa > 0
    assert isinstance(scaled_offset, int) and scaled_offset > 0
    return execute_schedule(LOADER6_PROGRAM,
                            {'x': x, 'scaled_kappa': scaled_kappa, 'scaled_offset': scaled_offset},
                            SWAPPED_OUTPUTS)


def verify_swapped_loaders():
    x, c, alpha, beta = sp.symbols('x c alpha beta')
    reports = {}
    for label, schedule, inputs, q, cost in (
        ('swapped_fixed_rank5', LOADER5_SWAPPED, {'x': x, 'c': c}, c*x, 5),
        ('preferred_uniform_program6', LOADER6_PROGRAM,
         {'x': x, 'scaled_kappa': alpha, 'scaled_offset': beta}, alpha*x+beta, 6)):
        available = set(inputs)
        for name, op, left, right in schedule:
            assert name not in available
            assert all(isinstance(v, int) or v in available for v in (left, right))
            available.add(name)
        counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in schedule)
        assert len(schedule) == cost and counts == {'M': 2, 'A': cost-2}
        actual = tuple(sp.expand(v) for v in execute_schedule(schedule, inputs, SWAPPED_OUTPUTS))
        Astar = (1, 1, 0, 1)
        direct = multiply(multiply((1, 0, -q, 1), Astar), (1, 0, q, 1))
        assert all(sp.expand(a-b) == 0 for a, b in zip(actual, direct))
        assert sp.expand(determinant(actual)-1) == 0
        degrees = [sp.Poly(v, x).degree() for v in actual]
        assert degrees == [1, 0, 2, 1]
        cases = 0
        for k in range(1, 9):
            generators = swapped_schreier_generators(k)
            assert generators[:2] == [Astar, (1, 0, 4*k, 1)]
            assert generators[2:] == [(1-4*i, 1, -16*i*i, 1+4*i) for i in range(1, k)]
            assert all(determinant(g) == 1 for g in generators)
            for program in range(12 if cost == 6 else 1):
                kappa, offset = 2**(program+1), 2**program
                for value in (-3, 0, 1, 2, 13, 97):
                    loaded = kappa*value+offset if cost == 6 else value
                    matrix = (loader6_program(value, 4*k*kappa, 4*k*offset) if cost == 6
                              else loader5_swapped(value, k))
                    Bstar = generators[1]
                    expected = multiply(multiply(matrix_power(Bstar, -loaded), Astar),
                                        matrix_power(Bstar, loaded))
                    assert matrix == expected
                    cases += 1
        reports[label] = dict(operations=cost, multiplications=2, additions_subtractions=cost-2,
                              supplied_witnesses=0, schedule=schedule, outputs=SWAPPED_OUTPUTS,
                              coordinate_polynomials=[str(v) for v in actual],
                              coordinate_degrees=degrees, determinant_identity=True,
                              symbolic_conjugation_identity=True, direct_integer_matrix_cases=cases,
                              fixed_rank_four_generators=dict(a=Astar, b=(1, 0, 12, 1)),
                              fixed_parameters=('c=4k with fixed rankN=k+1' if cost == 5 else
                                                'scaled_kappa=12*2^(p+1), scaled_offset=12*2^p for fixed program p'),
                              arithmetic_gates_use_only_nonnegative_literals=True,
                              fixed_numeral_products_charged=True, no_runtime_exponentiation=True)
    return reports


def verify():
    return dict(status='PASS_GROUP_UNIPOTENT_INPUT_LOADERS', quadratic_loaders={**verify_quadratic_loaders(), 'reference_uniform_program7': verify_affine_loader7(),
                                   **verify_swapped_loaders()},
                optional_commutator_loader=verify_commutator_loader(),
                conjugate_embedding=verify_embedding(), schreier_embedding=verify_schreier_embedding(),
                scope='Faithful free-group embedding and exact ordinary-input matrix curve only. No subgroup membership certificate, existential membership encoding, or universal Diophantine bound is provided.')


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
    for name, report in result['quadratic_loaders'].items():
        print(name, {key: report[key] for key in ('operations', 'multiplications', 'additions_subtractions', 'coordinate_degrees', 'supplied_witnesses')})
