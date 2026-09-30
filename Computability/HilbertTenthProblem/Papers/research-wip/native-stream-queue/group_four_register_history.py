#!/usr/bin/env python3
"""Four-register variable matrix-word interface; history typing is unpaid.

This checker uses only the Python standard library. It does not implement
an unbounded Diophantine history predicate or a subgroup membership oracle.
"""
from __future__ import annotations
import argparse
from collections import Counter
from itertools import product
import json
from pathlib import Path
import random

I = (1, 0, 0, 1)
# 0 is idle. The other labels update exactly one coordinate by +/- its mate.
ROWS = {0: None}
for coordinate in range(4):
    ROWS[2*coordinate+1] = (coordinate, coordinate ^ 1, 1)
    ROWS[2*coordinate+2] = (coordinate, coordinate ^ 1, -1)


def mul(a, b):
    return (a[0]*b[0]+a[1]*b[2], a[0]*b[1]+a[1]*b[3],
            a[2]*b[0]+a[3]*b[2], a[2]*b[1]+a[3]*b[3])


def det(a):
    return a[0]*a[3]-a[1]*a[2]


def inv(a):
    assert det(a) == 1
    return (a[3], -a[1], -a[2], a[0])


def action(a, v):
    return (a[0]*v[0]+a[1]*v[1], a[2]*v[0]+a[3]*v[1])


def letter_matrices(label):
    result = [I, I]
    if label:
        coordinate, _, sign = ROWS[label]
        result[coordinate//2] = ((1, sign, 0, 1) if coordinate % 2 == 0
                                else (1, 0, sign, 1))
    return tuple(result)


def word_matrices(word):
    answer = (I, I)
    for label in word:
        pair = letter_matrices(label)
        answer = tuple(mul(step, old) for step, old in zip(pair, answer))
    return answer


def inverse_letter(label):
    return 0 if label == 0 else (label+1 if label % 2 else label-1)


def inverse_word(word):
    return tuple(inverse_letter(label) for label in reversed(word))


def factor_sl2(matrix):
    """Return unit-shear action order s_0,... with s_last...s_0=matrix."""
    assert det(matrix) == 1
    current, row_word = matrix, []

    def row_operation(label):
        nonlocal current
        current = mul(letter_matrices(label)[0], current)
        row_word.append(label)

    def upper(amount):
        for _ in range(abs(amount)):
            row_operation(1 if amount > 0 else 2)

    def rotate():
        # Acting in this order gives [[0,1],[-1,0]].
        for label in (1, 4, 1):
            row_operation(label)

    while current[2]:
        quotient = current[0] // current[2]
        upper(-quotient)
        rotate()
    assert abs(current[0]) == 1
    if current[0] == -1:
        rotate()
        rotate()
    assert current[0] == current[3] == 1 and current[2] == 0
    upper(-current[1])
    assert current == I
    result = inverse_word(row_word)
    assert word_matrices(result) == (matrix, I)
    return result


def factor_pair(pair):
    first, second = map(factor_sl2, pair)
    result = first + tuple(label+4 for label in second)
    assert word_matrices(result) == pair
    return result


def accepts_macros(word, codes):
    """Recognize (idle | code_1 | ... | code_m)* by finite-word parsing."""
    # This is an exact bounded checker of the regular expression, not a
    # Diophantine representation of its arbitrarily long runs.
    reached = {0}
    for position in range(len(word)+1):
        if position not in reached:
            continue
        for code in ((0,), *codes):
            if tuple(word[position:position+len(code)]) == code:
                reached.add(position+len(code))
    return len(word) in reached


def target(r):
    return (1+r, 1, -r*r, 1-r)


def vector_trace(word, q):
    value = [q, 1, q, 1]
    states = [tuple(value)]
    for label in word:
        row = ROWS[label]
        if row is not None:
            destination, source, sign = row
            value[destination] += sign*value[source]
        states.append(tuple(value))
    return states


def pack(digits, base):
    answer = 0
    for digit in reversed(digits):
        answer = answer*base+digit
    return answer


def fields(word, positive_states, base):
    assert len(positive_states) == len(word)
    histories = [pack([state[i] for state in positive_states], base)
                 for i in range(4)]
    selectors, selected = [], []
    for label in range(1, 9):
        source = ROWS[label][1]
        mask = [int(current == label) for current in word]
        selectors.append(1+pack(mask, base))
        selected.append(1+pack([mask[j]*positive_states[j][source]
                                for j in range(len(word))], base))
    return histories, selectors, selected


class Circuit:
    def __init__(self):
        self.counts = Counter()
        self.schedule = []
        self.values = {}

    def gate(self, name, op, left, right):
        a = self.values[left] if isinstance(left, str) else left
        b = self.values[right] if isinstance(right, str) else right
        self.counts['M' if op == '*' else 'A'] += 1
        self.schedule.append((name, op, left, right))
        self.values[name] = a*b if op == '*' else a+b if op == '+' else a-b
        return self.values[name]


def boundary(circuit, x, alpha, beta, q):
    c = circuit
    c.values.update(x=x, alpha=alpha, beta=beta, q=q)
    c.gate('input_product', '*', 'alpha', 'x')
    c.gate('r', '+', 'input_product', 'beta')
    c.gate('D', '*', 'q', 'q')
    c.gate('c0', '+', 'D', 'q')
    c.gate('d0', '+', 'D', 1)
    c.gate('rq', '*', 'r', 'q')
    c.gate('z', '+', 'rq', 1)
    c.gate('U', '+', 'c0', 'z')
    c.gate('rz', '*', 'r', 'z')
    c.gate('V', '-', 'd0', 'rz')
    return tuple(c.values[name] for name in ('D', 'c0', 'd0', 'U', 'V'))


def aggregate(circuit, x, alpha, beta, q, length_power, hist, masks, selected):
    c = circuit
    boundary(c, x, alpha, beta, q)
    c.values['P'] = length_power
    c.gate('B', '*', 4, 'D')
    c.gate('UP', '*', 'U', 'P')
    c.gate('right_even', '-', 'UP', 'c0')
    c.gate('VP', '*', 'V', 'P')
    c.gate('right_odd', '-', 'VP', 'd0')
    residuals = []
    for i in range(4):
        for name, value in ((f'H{i}', hist[i]),
                            (f'S{i}p', masks[2*i]), (f'S{i}m', masks[2*i+1]),
                            (f'Z{i}p', selected[2*i]), (f'Z{i}m', selected[2*i+1])):
            c.values[name] = value
        c.gate(f'dZ{i}', '-', f'Z{i}p', f'Z{i}m')
        c.gate(f'dS{i}', '-', f'S{i}p', f'S{i}m')
        c.gate(f'DdS{i}', '*', 'D', f'dS{i}')
        c.gate(f'delta{i}', '-', f'dZ{i}', f'DdS{i}')
        c.gate(f'next{i}', '+', f'H{i}', f'delta{i}')
        c.gate(f'left{i}', '*', 'B', f'next{i}')
        c.gate(f'right{i}', '+', f'H{i}', 'right_odd' if i % 2 else 'right_even')
        # Equality comparison is free in the comparison-system ledger.
        residuals.append(c.values[f'left{i}']-c.values[f'right{i}'])
    return tuple(residuals)


def target_word(r):
    first = (3,)*r + (1,) + (4,)*r
    return first + tuple(label+4 for label in first)


def check():
    rng = random.Random(6010643)
    matrices = []
    for a, b, c in product(range(-7, 8), repeat=3):
        if a:
            numerator = 1+b*c
            if numerator % a == 0 and abs(numerator//a) <= 7:
                matrices.append((a, b, c, numerator//a))
        elif b*c == -1:
            matrices.extend((a, b, c, d) for d in range(-7, 8))
    for matrix in matrices:
        assert word_matrices(factor_sl2(matrix)) == (matrix, I)
    fixed_pairs = ((matrices[3], matrices[-4]), ((1, 2, 1, 3), (2, -1, -1, 1)))
    assert all(det(a) == det(b) == 1 for a, b in fixed_pairs)
    codes = tuple(factor_pair(pair) for pair in fixed_pairs)
    codes += tuple(inverse_word(code) for code in codes)
    macro_cases = 0
    for _ in range(128):
        choices = [rng.randrange(len(codes)) for _ in range(rng.randrange(8))]
        word = (0, 0) + sum((codes[i]+(0,) for i in choices), ())
        assert accepts_macros(word, codes)
        expected = (I, I)
        for index in choices:
            pair = word_matrices(codes[index])
            expected = tuple(mul(step, old) for step, old in zip(pair, expected))
        assert word_matrices(word) == expected
        macro_cases += 1

    word_count = action_tests = 0
    words = [word for length in range(2, 6)
             for word in product(range(9), repeat=length)]
    words += [tuple(rng.randrange(9) for _ in range(rng.randrange(2, 65)))
              for _ in range(512)]
    for word in words:
        t, q = len(word), 2**len(word)
        pair = word_matrices(word)
        assert all(det(matrix) == 1 and max(map(abs, matrix)) <= q//2
                   for matrix in pair)
        states = vector_trace(word, q)
        assert states[-1] == tuple(value for matrix in pair for value in action(matrix, (q, 1)))
        assert all(abs(value) < q*q for state in states for value in state)
        # A bounded audit of the exact one-vector implication, with no input bound.
        for r in (0, 1, 2, q+7):
            vector = action(target(r), (q, 1))
            for matrix in pair:
                assert (action(matrix, (q, 1)) == vector) == (matrix == target(r))
                action_tests += 1
        word_count += 1

    c = Circuit()
    D, c0, d0, U, V = boundary(c, 17, 24, 12, 256)
    assert c.counts == {'M': 4, 'A': 6}
    assert (U-D, V-D) == action(target(24*17+12), (256, 1))
    boundary_schedule = list(c.schedule)
    faithful_cases = mutation_cases = random_typed_cases = 0
    complete_schedule = None
    program_fixtures = [(r, 1, 0) for r in range(1, 13)] + [(x, 24, 12) for x in range(1, 4)]
    for x, alpha, beta in program_fixtures:
        r = alpha*x+beta
        word = (0, 0) + target_word(r) + (0,)
        t, q = len(word), 2**len(word)
        D, B = q*q, 4*q*q
        P = B**t
        actual = vector_trace(word, q)
        shifted = [tuple(D+v for v in state) for state in actual[:-1]]
        assert all(0 < v < 2*D for state in shifted for v in state)
        args = fields(word, shifted, B)
        assert all(v > 0 for field in args for v in field)
        circuit = Circuit()
        assert aggregate(circuit, x, alpha, beta, q, P, *args) == (0, 0, 0, 0)
        assert circuit.counts == {'M': 15, 'A': 28}
        assert len(circuit.schedule) == 43
        assert word_matrices(word) == (target(r), target(r))
        assert (circuit.values['U'], circuit.values['V'])*2 == tuple(D+v for v in actual[-1])
        complete_schedule = circuit.schedule
        faithful_cases += 1
        # Change one pre-state digit, rebuilding the selected fields consistently.
        for _ in range(8):
            position, coordinate = rng.randrange(t), rng.randrange(4)
            changed = list(shifted)
            row = list(changed[position])
            row[coordinate] += 1
            assert 0 < row[coordinate] < 2*D
            changed[position] = tuple(row)
            args = fields(word, changed, B)
            assert any(aggregate(Circuit(), x, alpha, beta, q, P, *args))
            mutation_cases += 1

    # Arbitrary correctly typed selected fields: aggregate equations agree with
    # the direct local recurrence/boundary test, including deliberately false data.
    for _ in range(2048):
        t = rng.randrange(2, 9)
        word = tuple(rng.randrange(9) for _ in range(t))
        q, r = 2**t, rng.randrange(1, 20)
        D, B = q*q, 4*q*q
        shifted = [tuple(rng.randrange(1, 2*D) for _ in range(4)) for _ in range(t)]
        args = fields(word, shifted, B)
        residuals = aggregate(Circuit(), r, 1, 0, q, B**t, *args)
        wanted = vector_trace(word, q)
        boundary_match = wanted[-1] == action(target(r), (q, 1))*2
        interior_match = shifted == [tuple(D+v for v in state) for state in wanted[:-1]]
        assert (not any(residuals)) == (boundary_match and interior_match)
        random_typed_cases += 1

    # Removing the height condition permits an exact false matrix identification.
    q, r = 4, 2
    stabilizer = (1-q, q*q, -1, 1+q)
    false = mul(target(r), stabilizer)
    assert det(stabilizer) == det(false) == 1
    assert action(false, (q, 1)) == action(target(r), (q, 1))
    assert false != target(r) and max(map(abs, false)) > q//2

    return dict(
        scope='Exact variable-length four-register reduction and conditional packed interface; no complete Diophantine history predicate',
        elementary_letters=ROWS,
        matrix_factorization_cases=len(matrices), regular_macro_cases=macro_cases,
        signed_shear_words=word_count, matrix_action_equivalence_cases=action_tests,
        entry_bound='max|P_j entry| <= 2^(j-1) for j>=1',
        geometry='t>=2, q=2^t; D=q^2; B=4D; P=B^t',
        vector_bound='every intermediate signed coordinate has absolute value < q^2',
        target='L_r=[[1+r,1],[-r^2,1-r]], r=alpha*x+beta',
        ordinary_input='x>0; fixed positive program numerals alpha,beta; no coded-input replacement',
        boundary=dict(operations=10, multiplications=4, additions_subtractions=6,
                      supplied_witnesses=0, schedule=boundary_schedule),
        conditional_aggregate=dict(operations=43, multiplications=15,
                                   additions_subtractions=28, equations=4,
                                   strictly_positive_history_fields=20,
                                   geometry_parameters=['q', 'P'], schedule=complete_schedule,
                                   unpaid=['q=2^t and P=B^t with same t',
                                           'bounded digits of four histories',
                                           'eight synchronized one-hot-or-idle selectors',
                                           'eight selected-source Hadamard fields',
                                           'regular macro language']),
        faithful_positive_history_cases=faithful_cases,
        rebuilt_selection_mutation_cases=mutation_cases,
        arbitrary_typed_history_cases=random_typed_cases,
        height_necessity_counterexample=dict(q=q, r=r, target=target(r), false_matrix=false),
        mathematical_proofs='See sibling Markdown; finite tests do not establish unbounded freeness, matrix-word selection, or Diophantine definability')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    answer = check()
    path = Path(__file__).with_suffix('.json')
    encoded = json.dumps(answer, indent=2, sort_keys=True)+'\n'
    if args.write:
        path.write_text(encoded)
        print(f'Wrote {path.name}')
    else:
        assert json.loads(path.read_text()) == json.loads(encoded), 'receipt mismatch'
        print('PASS: four-register matrix history and conditional43 ledger')


if __name__ == '__main__':
    main()
