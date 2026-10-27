#!/usr/bin/env python3
"""Check fixed exact support certificates for the 9/4 rectangular backend.

Standard-library only. No floating-point value is used for acceptance.
This verifies finite inequalities, not a complete SAT algorithm.
"""
from fractions import Fraction
from itertools import combinations, permutations
from pathlib import Path
import argparse
import json

SCALE = 21_400_000
WEIGHTS = sorted(set(permutations((21_400_107, 21_400_107, 0))) |
                 set(permutations((21_400_000, 16_750_214, 10_000_000))))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def operation_parts(r, blocks):
    require(len(blocks) == 3 and all(blocks), 'Three nonempty blocks required')
    require(sorted(x for b in blocks for x in b) == list(range(r)), 'Bad partition')
    parts = []
    universe = set(range(r))

    def build(block):
        if len(block) == 1:
            return
        midpoint = len(block) // 2
        left, right = block[:midpoint], block[midpoint:]
        build(left)
        build(right)
        parts.append((left, right, sorted(universe - set(block))))

    for block in blocks:
        build(block)
    parts.append(blocks)
    require(len(parts) == r - 2, 'Wrong operation count')
    return parts


def supports(r, blocks):
    edges = list(combinations(range(r), 2))
    result = []
    for parts in operation_parts(r, blocks):
        labels = {v: j for j, part in enumerate(parts) for v in part}
        for weights in WEIGHTS:
            coefficients = dict(zip(((0, 1), (0, 2), (1, 2)), weights))
            result.append(tuple(
                0 if labels[x] == labels[y] else
                coefficients[tuple(sorted((labels[x], labels[y])))]
                for x, y in edges))
    return result


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def verify_backend_supports():
    count = 0
    for x in range(13):
        for y in range(13):
            for z in range(13):
                a, b, c = sorted((x, y, z), reverse=True)
                direct = max(21_400_107 * (a + b),
                             21_400_000 * a + 16_750_214 * b + 10_000_000 * c)
                supported = max(w[0] * x + w[1] * y + w[2] * z
                                for w in WEIGHTS)
                require(direct == supported, 'Support identity failed')
                count += 1
    # Algebraic justification for all nonnegative triples: each branch's
    # sorted coefficients are nonincreasing, so rearrangement applies.
    require(21_400_000 >= 16_750_214 >= 10_000_000 >= 0, 'Coefficient order')
    return count


def certificate(r, plans, expected):
    q = len(plans)
    menus = [supports(r, p) for p in plans]
    norms = [[dot(v, v) for v in menu] for menu in menus]
    pairs = []
    if q == 1:
        upper = Fraction(2 * max(norms[0]), SCALE * SCALE * r * r)
        pair_choices = 0
    else:
        pair_choices = 0
        for i, j in combinations(range(q), 2):
            best = None
            witness = None
            for k, v in enumerate(menus[i]):
                for ell, w in enumerate(menus[j]):
                    value = norms[i][k] + norms[j][ell] + 2 * (q - 1) * dot(v, w)
                    if best is None or value > best:
                        best, witness = value, [k, ell]
                    pair_choices += 1
            pairs.append({'i': i, 'j': j, 'maximum': best, 'witness': witness})
        total = sum(p['maximum'] for p in pairs)
        upper = Fraction(2 * total, (q - 1) * q * q * SCALE * SCALE * r * r)
    require(upper == Fraction(expected), f'Changed certificate for r={r}')
    result = {'r': r, 'plans': q, 'supports_per_plan': 9 * (r - 2),
              'pair_choices_checked': pair_choices, 'beta_squared': str(upper),
              'pair_maxima': pairs}
    if r == 9:
        a = Fraction(335, 428) + Fraction(1, 100000)
        b = Fraction(50, 107)
        closed = (3 * (1 + a * a + b * b) + 2 * (1 + a + b) ** 2) / 54
        require(upper == closed, 'Affine closed form differs')
        require(all(p['maximum'] == 42914851341773880 for p in pairs),
                'Affine uniform maxima differ')
        categories = {}
        # The first six operations alternate point merge / line completion.
        labels = ['P', 'L', 'P', 'L', 'P', 'L', 'R']
        for i, j in combinations(range(q), 2):
            for k, v in enumerate(menus[i]):
                for ell, w in enumerate(menus[j]):
                    key = ','.join(sorted((labels[k // 9], labels[ell // 9])))
                    value = norms[i][k] + norms[j][ell] + 6 * dot(v, w)
                    categories[key] = max(categories.get(key, 0), value)
        expected_categories = {
            'P,P': 32057520572801430, 'L,P': 33889378891247226,
            'P,R': 35253600044884614, 'L,L': 38469024687361716,
            'L,R': 40520203014567798, 'R,R': 42914851341773880}
        require(categories == expected_categories, 'Affine category maxima differ')
        result['category_maxima'] = categories
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data', type=Path,
                        default=Path(__file__).resolve().parent.parent / 'data' / 'new_backend_plans.json')
    args = parser.parse_args()
    data = json.loads(args.data.read_text())
    results = [certificate(row['r'], row['plans'], row['beta_squared'])
               for row in data]
    print(json.dumps({'status': 'PASS',
                      'backend_support_samples': verify_backend_supports(),
                      'certificates': results}, indent=2))


if __name__ == '__main__':
    main()
