#!/usr/bin/env python3
"""Replay the S4 proof using Python's exact integers and rational numbers.

No numerical values, matrix ranks, PSLQ output, pickle, or third-party
packages are used.  Each relation is regenerated from its mathematical
input descriptor before the supplied rational combination is checked.

A multiple polylogarithm is ((s1,c1),...,(sr,cr)), meaning arguments
(i**c1,...,i**cr).  In integral words -1 denotes the zero letter and
0,1,2,3 denote the nonzero letters 1,i,-1,-i.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path
import argparse
import json


def freeze(value):
    return tuple(map(freeze, value)) if isinstance(value, list) else value


def add(out, row, coefficient=1):
    for key, value in row.items():
        out[key] = out.get(key, 0) + coefficient * value
        if not out[key]:
            del out[key]
    return out


def admissible(z):
    return bool(z) and z[0] != (1, 0)


def to_word(z):
    result, color = [], 0
    for weight, exponent in z:
        assert weight >= 1 and exponent in range(4)
        color = (color - exponent) % 4
        result.extend([-1] * (weight - 1) + [color])
    return tuple(result)


def from_word(word):
    result, weight, previous = [], 1, 0
    for letter in word:
        if letter == -1:
            weight += 1
        else:
            result.append((weight, (previous - letter) % 4))
            weight, previous = 1, letter
    assert weight == 1, "An integral word must not end in the zero letter."
    return tuple(result)


def shuffle(left, right):
    """Enumerate positions directly, independently of discovery recursion."""
    u, v = to_word(left), to_word(right)
    result = Counter()
    for positions in combinations(range(len(u) + len(v)), len(u)):
        positions = set(positions)
        iu = iv = 0
        word = []
        for j in range(len(u) + len(v)):
            if j in positions:
                word.append(u[iu])
                iu += 1
            else:
                word.append(v[iv])
                iv += 1
        result[from_word(word)] += 1
    return dict(result)


def stuffle(left, right):
    if not left:
        return {right: 1}
    if not right:
        return {left: 1}
    result = {}
    for tail, coefficient in stuffle(left[1:], right).items():
        add(result, {(left[0],) + tail: coefficient})
    for tail, coefficient in stuffle(left, right[1:]).items():
        add(result, {(right[0],) + tail: coefficient})
    merged = (left[0][0] + right[0][0],
              (left[0][1] + right[0][1]) % 4)
    for tail, coefficient in stuffle(left[1:], right[1:]).items():
        add(result, {(merged,) + tail: coefficient})
    return result


def imaginary(row):
    result = {}
    for value, coefficient in row.items():
        conjugate = tuple((weight, (-color) % 4) for weight, color in value)
        if value < conjugate:
            add(result, {value: coefficient})
        elif conjugate < value:
            add(result, {conjugate: -coefficient})
    return result


def distribution(z):
    """Li_s(z**2) - 2**(weight-depth) sum_signs Li_s(signs*z)."""
    assert all(color in (0, 1) for _, color in z)
    assert z[0] != (1, 0), "Only convergent distribution is used."
    weight = sum(a for a, _ in z)
    result = {tuple((a, (2 * color) % 4) for a, color in z): 1}
    for shifts in product((0, 2), repeat=len(z)):
        value = tuple((a, (color + shift) % 4)
                      for (a, color), shift in zip(z, shifts))
        add(result, {value: -2 ** (weight - len(z))})
    return result


def standard_relation(descriptor):
    kind = descriptor[0]
    if kind == 'ds':
        left, right = descriptor[1:]
        assert admissible(right)
        assert admissible(left) or left == ((1, 0),)
        row = add(shuffle(left, right), stuffle(left, right), -1)
    elif kind == 'lift':
        seed, multiplier = descriptor[1:]
        assert seed[0] == 'dist'
        assert not multiplier or admissible(multiplier)
        row = {}
        for value, coefficient in distribution(seed[1]).items():
            add(row, shuffle(value, multiplier), coefficient)
    else:
        raise AssertionError('Unknown relation schema: ' + str(kind))
    assert all(admissible(value) for value in row)
    return imaginary(row)


def duality_relation(value):
    word = to_word(value)
    assert word[0] != 0 and word[-1] != -1
    image = {-1: 0, 0: -1, 1: 3, 2: None, 3: 1}
    polynomial = {(): 1}
    for letter in reversed(word):
        choices = {2: -1}
        if image[letter] is not None:
            choices[image[letter]] = 1
        polynomial = {prefix + (new_letter,): c * d
                      for prefix, c in polynomial.items()
                      for new_letter, d in choices.items()}
    result = {value: 1}
    for transformed_word, coefficient in polynomial.items():
        transformed = from_word(transformed_word)
        assert admissible(transformed)
        sign = (-1) ** (len(word) + len(value) + len(transformed))
        add(result, {transformed: -sign * coefficient})
    return imaginary(result)


def target_relation():
    result = {((4, 1), (1, 2)): 1120,
              ((4, 1), (1, 0)): 480,
              ((3, 1), (2, 0)): 480,
              ((2, 1), (3, 0)): 1440,
              ((5, 1),): -1536}
    add(result, shuffle(((2, 1),), ((3, 0),)), 135)
    add(result, shuffle(((4, 1),), ((1, 2),)), -2240)
    return imaginary(result)


def verify(path):
    data = json.loads(path.read_text())
    target = target_relation()
    assert {freeze(value): coefficient
            for value, coefficient in data['target_as_words']} == target
    residual = target.copy()
    seed = freeze(data['duality']['indices_colors'])
    assert seed == ((1, 1), (4, 0))
    dual_coefficient = Fraction(data['duality']['coefficient'])
    assert dual_coefficient == -1120
    add(residual, duality_relation(seed), -dual_coefficient)
    counts = Counter()
    for entry in data['standard_relations']:
        descriptor = freeze(entry['relation'])
        coefficient = Fraction(entry['coefficient'])
        assert coefficient
        row = standard_relation(descriptor)
        assert all(sum(a for a, _ in value) == 5 for value in row)
        add(residual, row, -coefficient)
        kind = descriptor[0]
        if kind == 'ds' and descriptor[1] == ((1, 0),):
            kind = 'regularized_ds'
        counts[kind] += 1
    assert not residual, 'Nonzero exact residual: ' + str(residual)
    return {'verified': True, 'arithmetic': 'exact rational',
            'standard_relations': len(data['standard_relations']),
            'relation_counts': dict(counts),
            'duality_relations': 1, 'residual_terms': 0}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('certificate', nargs='?', type=Path,
                        default=Path(__file__).resolve().parents[1] / 'results' / 'S4_certificate.json')
    arguments = parser.parse_args()
    print(json.dumps(verify(arguments.certificate), indent=2, sort_keys=True))
