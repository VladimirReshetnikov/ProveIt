#!/usr/bin/env python3
"""Uniform two-generator H^r membership and a three-letter order obstruction.

Coordinates (a,b,c) denote [[1,a,c],[0,1,b],[0,0,1]].  Fixed generator
coordinates are compile-time integers; target coordinates are relation
arguments. Four supplied witnesses are strictly positive. No Roman'kov
universal monoid is constructed or numerically verified here.
"""
import argparse
from itertools import combinations, permutations, product
import json
from math import gcd
from pathlib import Path
import random


IDENTITY = (0, 0, 0)


def multiply(left, right):
    a, b, c = left
    d, e, f = right
    return a+d, b+e, c+f+a*e


def inverse(value):
    a, b, c = value
    return -a, -b, a*b-c


def power(value, exponent):
    if exponent < 0:
        value, exponent = inverse(value), -exponent
    result = IDENTITY
    while exponent:
        if exponent & 1:
            result = multiply(result, value)
        value = multiply(value, value)
        exponent //= 2
    return result


def evaluate(word, generators):
    answer = (IDENTITY,)*len(generators[0])
    for letter in word:
        answer = tuple(multiply(a, b) for a, b in zip(answer, generators[letter]))
    return answer


def statistics(word):
    n = m = pairs = 0
    for letter in word:
        if letter == 0:
            n += 1
        else:
            assert letter == 1
            pairs += n
            m += 1
    return n, m, pairs


def realize(n, m, pairs):
    assert min(n, m, pairs) >= 0 and pairs <= n*m
    if not n:
        return (1,)*m
    quotient, remainder = divmod(pairs, n)
    if quotient == m:
        assert remainder == 0
        return (0,)*n+(1,)*m
    return ((1,)*(m-quotient-1)+(0,)*remainder+(1,)
            +(0,)*(n-remainder)+(1,)*quotient)


def formula(first, second, n, m, pairs):
    result = []
    for (a, b, c), (d, e, f) in zip(first, second):
        result.append((n*a+m*d, n*b+m*e,
                       n*c+m*f+n*(n-1)//2*a*b+m*(m-1)//2*d*e
                       +pairs*a*e+(n*m-pairs)*d*b))
    return tuple(result)


class Circuit:
    def __init__(self):
        self.counts = {'M': 0, 'A': 0}

    def add(self, left, right):
        self.counts['A'] += 1
        return left+right

    def sub(self, left, right):
        self.counts['A'] += 1
        return left-right

    def mul(self, left, right):
        self.counts['M'] += 1
        return left*right


def source(circuit, first, second, target, supplied, one=False):
    """Literal generic schedule; even zero/one fixed-coefficient products count."""
    N, M, K, W = supplied
    n, m, pairs = (circuit.sub(v, 1) for v in (N, M, K))
    pn = circuit.mul(n, circuit.sub(n, 1))
    pm = circuit.mul(m, circuit.sub(m, 1))
    nm = circuit.mul(n, m)
    sides = [(circuit.add(K, W), circuit.add(nm, 2))]
    for (a, b, c), (d, e, f), (A, B, C) in zip(first, second, target):
        sides.append((A, circuit.add(circuit.mul(a, n), circuit.mul(d, m))))
        sides.append((B, circuit.add(circuit.mul(b, n), circuit.mul(e, m))))
        # Constants below depend only on the two fixed generators.
        terms = [circuit.mul(2*c, n), circuit.mul(2*f, m),
                 circuit.mul(a*b, pn), circuit.mul(d*e, pm),
                 circuit.mul(2*d*b, nm), circuit.mul(2*(a*e-d*b), pairs)]
        central = terms[0]
        for term in terms[1:]:
            central = circuit.add(central, term)
        sides.append((circuit.add(C, C), central))
    if not one:
        return tuple(left-right for left, right in sides)
    squares = [circuit.mul(residual, residual)
               for left, right in sides for residual in [circuit.sub(left, right)]]
    answer = squares[0]
    for square in squares[1:]:
        answer = circuit.add(answer, square)
    return answer


def manual_residuals(first, second, target, supplied):
    N, M, K, W = supplied
    n, m, pairs = N-1, M-1, K-1
    residuals = [K+W-n*m-2]
    for (a, b, c), (d, e, f), (A, B, C) in zip(first, second, target):
        residuals += [A-n*a-m*d, B-n*b-m*e,
                      2*C-2*n*c-2*m*f-n*(n-1)*a*b-m*(m-1)*d*e
                      -2*pairs*a*e-2*(n*m-pairs)*d*b]
    return tuple(residuals)


def positive_witnesses(n, m, pairs):
    assert 0 <= pairs <= n*m and min(n, m) >= 0
    return n+1, m+1, pairs+1, n*m-pairs+1


def bezout(a, b):
    old_r, r, old_s, s, old_t, t = abs(a), abs(b), 1, 0, 0, 1
    while r:
        q = old_r//r
        old_r, r = r, old_r-q*r
        old_s, s = s, old_s-q*s
        old_t, t = t, old_t-q*t
    return old_r, old_s*(1 if a >= 0 else -1), old_t*(1 if b >= 0 else -1)


def nonnegative_linear_pair(a, b, target):
    if a == b == 0:
        return (0, 0) if target == 0 else None
    divisor, u, v = bezout(a, b)
    assert a*u+b*v == divisor == gcd(a, b)
    if target % divisor:
        return None
    bases = (u*(target//divisor), v*(target//divisor))
    steps = (b//divisor, -a//divisor)
    lower = upper = None
    for base, step in zip(bases, steps):
        if step == 0:
            if base < 0:
                return None
        elif step > 0:
            bound = -(base//step)
            lower = bound if lower is None else max(lower, bound)
        else:
            bound = (-base)//step
            upper = bound if upper is None else min(upper, bound)
    if lower is not None and upper is not None and lower > upper:
        return None
    parameter = lower if lower is not None else upper if upper is not None else 0
    result = tuple(base+step*parameter for base, step in zip(bases, steps))
    assert min(result) >= 0 and a*result[0]+b*result[1] == target
    return result


def solve_two_column(first, second, target):
    row = next((i for i, (a, b) in enumerate(zip(first, second)) if a or b), None)
    if row is None:
        return (0, 0) if not any(target) else None
    independent = next((i for i in range(len(first))
                        if first[row]*second[i]-first[i]*second[row]), None)
    if independent is None:
        candidate = nonnegative_linear_pair(first[row], second[row], target[row])
    else:
        i, j = row, independent
        determinant = first[i]*second[j]-first[j]*second[i]
        numerators = (target[i]*second[j]-target[j]*second[i],
                      first[i]*target[j]-first[j]*target[i])
        if any(value % determinant for value in numerators):
            return None
        candidate = tuple(value//determinant for value in numerators)
    if candidate is None or min(candidate) < 0:
        return None
    n, m = candidate
    return candidate if all(a*n+b*m == c for a, b, c in zip(first, second, target)) else None


def log_coordinates(value):
    return tuple(coordinate for a, b, c in value for coordinate in (2*a, 2*b, 2*c-a*b))


def decide_membership(first, second, target):
    noncommuting = next((i for i, ((a, b, c), (d, e, f)) in enumerate(zip(first, second))
                        if a*e-d*b), None)
    if noncommuting is None:
        candidate = solve_two_column(log_coordinates(first), log_coordinates(second), log_coordinates(target))
        if candidate is None:
            return None
        n, m = candidate
        assert formula(first, second, n, m, 0) == target
        return n, m, 0
    (a, b, c), (d, e, f), (A, B, C) = first[noncommuting], second[noncommuting], target[noncommuting]
    determinant = a*e-d*b
    numerators = (A*e-d*B, a*B-A*b)
    if any(value % determinant for value in numerators):
        return None
    n, m = (value//determinant for value in numerators)
    if min(n, m) < 0:
        return None
    baseline = n*c+m*f+n*(n-1)//2*a*b+m*(m-1)//2*d*e+n*m*d*b
    if (C-baseline) % determinant:
        return None
    pairs = (C-baseline)//determinant
    if not 0 <= pairs <= n*m or formula(first, second, n, m, pairs) != target:
        return None
    return n, m, pairs


def realization_checks():
    observed = {}
    words = 0
    for length in range(11):
        for word in product((0, 1), repeat=length):
            n, m, pairs = statistics(word)
            observed.setdefault((n, m), set()).add(pairs)
            words += 1
    for (n, m), values in observed.items():
        assert values == set(range(n*m+1))
    constructions = 0
    for n, m in product(range(13), repeat=2):
        for pairs in range(n*m+1):
            assert statistics(realize(n, m, pairs)) == (n, m, pairs)
            constructions += 1
    return dict(exhaustive_binary_words=words, count_pairs=len(observed),
                exact_realizations=constructions, includes_empty_word_and_zero_counts=True)


def certificate_checks():
    rng = random.Random(206071)
    valid = mutations = arbitrary = 0
    for _ in range(1024):
        rank = rng.randrange(1, 6)
        first, second = [tuple(tuple(rng.randrange(-4, 5) for _ in range(3)) for _ in range(rank))
                         for _ in range(2)]
        word = tuple(rng.randrange(2) for _ in range(rng.randrange(25)))
        n, m, pairs = statistics(word)
        target = evaluate(word, (first, second))
        assert target == formula(first, second, n, m, pairs)
        supplied = positive_witnesses(n, m, pairs)
        for one in (False, True):
            circuit = Circuit()
            assert source(circuit, first, second, target, supplied, one) == (0 if one else (0,)*(3*rank+1))
            assert circuit.counts == {'M':10*rank+3+(3*rank+1)*one,
                                      'A':8*rank+7+(6*rank+1)*one}
        answer = decide_membership(first, second, target)
        assert answer is not None and evaluate(realize(*answer), (first, second)) == target
        for coordinate in range(3):
            wrong = [list(block) for block in target]
            wrong[0][coordinate] += 1
            assert source(Circuit(), first, second, wrong, supplied, True) == (4 if coordinate == 2 else 1)
            mutations += 1
        valid += 1
    for _ in range(2048):
        rank = rng.randrange(1, 6)
        first, second, target = [tuple(tuple(rng.randrange(-12, 13) for _ in range(3)) for _ in range(rank))
                                 for _ in range(3)]
        supplied = tuple(rng.randrange(1, 20) for _ in range(4))
        expected = manual_residuals(first, second, target, supplied)
        for one in (False, True):
            circuit = Circuit()
            actual = source(circuit, first, second, target, supplied, one)
            assert actual == (sum(value*value for value in expected) if one else expected)
            assert circuit.counts == {'M':10*rank+3+(3*rank+1)*one,
                                      'A':8*rank+7+(6*rank+1)*one}
        arbitrary += 1
    return dict(actual_word_certificates=valid, target_coordinate_mutations=mutations,
                arbitrary_positive_assignment_identity_checks=arbitrary,
                graph='18r+10 = (10r+3)M+(8r+7)A', equations='3r+1',
                positive_witnesses=4, polynomial='27r+12 = (13r+4)M+(14r+8)A',
                polynomial_degree_at_most=4)


def decision_checks():
    linear = noncommuting = commuting = 0
    for a, b, target in product(range(-4, 5), range(-4, 5), range(-10, 11)):
        expected = any(a*n+b*m == target for n, m in product(range(31), repeat=2))
        answer = nonnegative_linear_pair(a, b, target)
        assert (answer is not None) == expected
        linear += 1
    # A and B force the two counts, so this enumeration has an exact
    # completeness bound and can independently test negative centers.
    first, second = ((1, 0, 0),), ((0, 1, 0),)
    for n, m, central in product(range(7), range(7), range(-2, 40)):
        target = ((n, m, central),)
        answer = decide_membership(first, second, target)
        assert (answer is not None) == (0 <= central <= n*m)
        noncommuting += 1
    rng = random.Random(206072)
    for _ in range(512):
        base = tuple(tuple(rng.randrange(-2, 3) for _ in range(3)) for _ in range(3))
        u, v = rng.randrange(-4, 5), rng.randrange(-4, 5)
        first = tuple(power(block, u) for block in base)
        second = tuple(power(block, v) for block in base)
        exponent = rng.randrange(-12, 13)
        target = tuple(power(block, exponent) for block in base)
        answer = decide_membership(first, second, target)
        expected = True if all(block == IDENTITY for block in base) else nonnegative_linear_pair(u, v, exponent) is not None
        assert (answer is not None) == expected
        if answer is not None:
            assert evaluate(realize(*answer), (first, second)) == target
        commuting += 1
    return dict(signed_linear_diophantine_cases=linear,
                noncommuting_exact_positive_and_negative_targets=noncommuting,
                commuting_power_family_targets=commuting,
                scope='Decidability proof uses exact rank/gcd cases, not these bounded tests.')


def cyclic_order_obstruction():
    tracked_pairs = ((0, 1), (1, 2), (2, 0))
    generators = tuple(tuple((1, 0, 0) if letter == first else (0, 1, 0) if letter == second else IDENTITY
                             for first, second in tracked_pairs) for letter in range(3))
    target = ((1, 1, 1),)*3
    impossible_pair_counts = {(i, j): int((i, j) in tracked_pairs)
                              for i, j in product(range(3), repeat=2)}
    for i in range(3):
        assert impossible_pair_counts[i, i] == 0
        for j in range(3):
            if i != j:
                assert 0 <= impossible_pair_counts[i, j] <= 1
                assert impossible_pair_counts[i, j]+impossible_pair_counts[j, i] == 1
    relaxed = []
    for block in range(3):
        a = sum(g[block][0] for g in generators)
        b = sum(g[block][1] for g in generators)
        c = sum(g[block][2] for g in generators)
        c += sum(impossible_pair_counts[i, j]*generators[i][block][0]*generators[j][block][1]
                 for i, j in product(range(3), repeat=2))
        relaxed.append((a, b, c))
    assert tuple(relaxed) == target
    actual = [evaluate(word, generators) for word in permutations(range(3))]
    assert target not in actual
    return dict(heisenberg_factors=3, monoid_generators=generators, target=target,
                relaxed_count_witness=[1, 1, 1], cyclic_pair_counts=impossible_pair_counts_to_list(impossible_pair_counts),
                all_possible_words_checked=6,
                completeness='The horizontal target coordinates force exactly one occurrence of each generator.',
                conclusion='Nonnegative letter counts, same-letter triangular counts, opposite-pair sums '
                           'and all pair bounds do not guarantee a realizable word.')


def impossible_pair_counts_to_list(values):
    return [[values[i, j] for j in range(3)] for i in range(3)]


def three_statistics(word):
    counts, pairs = [0, 0, 0], [[0]*3 for _ in range(3)]
    for letter in word:
        for i in range(3):
            pairs[i][letter] += counts[i]
        counts[letter] += 1
    return tuple(counts), (pairs[0][1], pairs[1][2], pairs[2][0])


def interior_order_obstruction():
    checked_words = attainable_witnesses = 0
    records = []
    for m in range(3, 11):
        total = m+4
        spectrum, all_triples = set(), set()
        for b_positions in combinations(range(total), 2):
            remaining = [i for i in range(total) if i not in b_positions]
            for c_positions in combinations(remaining, 2):
                word = tuple(1 if i in b_positions else 2 if i in c_positions else 0
                             for i in range(total))
                counts, triple = three_statistics(word)
                assert counts == (m, 2, 2)
                all_triples.add(triple)
                if triple[:2] == (1, 1):
                    spectrum.add(triple[2])
                checked_words += 1
        assert spectrum == {2*m-1, 2*m}
        fake = (1, 1, 2*m-2)
        assert fake not in all_triples
        assert 0 < fake[0] < 2*m and 0 < fake[1] < 4 and 0 < fake[2] < 2*m
        weighted = 2*fake[0]+m*fake[1]+2*fake[2]
        assert 4*m < weighted == 5*m-2 < 8*m
        words = ((2, 1, 0, 2, 1)+(0,)*(m-1), (2, 1, 2, 0, 1)+(0,)*(m-1))
        for expected, word in zip((2*m-1, 2*m), words):
            assert three_statistics(word) == ((m, 2, 2), (1, 1, expected))
            attainable_witnesses += 1
        relaxed = {(a, b, c) for a, b, c in product(range(2*m+1), range(5), range(2*m+1))
                   if 4*m <= 2*a+m*b+2*c <= 8*m}
        assert all_triples <= relaxed
        if m == 3:
            assert len(all_triples) == 127 and len(relaxed) == 155
        records.append(dict(first_letter_count=m, exact_triples=len(all_triples),
                            box_and_weighted_triangle_triples=len(relaxed),
                            conditional_spectrum=sorted(spectrum), excluded_interior_triple=fake))
    return dict(multiset_words_checked=checked_words, endpoint_spectrum_witnesses=attainable_witnesses,
                finite_records=records,
                general_family='n=(m,2,2), K_AB=K_BC=1, K_CA=2m-2, every integer m>=3',
                conclusion='Every directed pair count is strictly interior, and both weighted triangle '
                           'inequalities are strict, but no word realizes these data.')


def verify():
    return dict(status='PASS_HEISENBERG_TWO_GENERATOR_MEMBERSHIP',
                realization=realization_checks(), certificate=certificate_checks(),
                decision=decision_checks(), three_letter_obstruction=cyclic_order_obstruction(),
                interior_order_obstruction=interior_order_obstruction(),
                primary_source=dict(url='https://arxiv.org/abs/2209.14786',
                                    sections='Sections 2,4; Theorems 5.1 and 5.2',
                                    factors='8e+4d+q+1', monoid_generators='14e+7d',
                                    fixed_numeric_dimension='Not instantiated independently of a chosen Diophantine/Skolem system.',
                                    universality_dependency='The fixed undecidable monoid is compiled from a fixed Diophantine polynomial.',
                                    signed_parameter_caveat='The displayed |nu| target and monoid independence from nu cannot '
                                                            'jointly hold over all signed nu: D(z)=z^2 distinguishes +/-1. '
                                                            'Restrict to one sign or repair the sign encoding.'),
                limits='The two-generator theorem is uniform and constructive, but every such monoid has decidable '
                       'membership. The three-letter example blocks the naive pair-count relaxation, not every '
                       'possible arithmetic encoding. No universal monoid or improved complete Diophantine bound is supplied.')


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
    print('H^r two-generator membership: 4 positive witnesses; graph18r+10; polynomial27r+12; decidable.')
