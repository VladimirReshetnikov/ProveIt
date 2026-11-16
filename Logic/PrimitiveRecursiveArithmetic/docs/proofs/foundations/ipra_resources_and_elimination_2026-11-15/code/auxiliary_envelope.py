"""Finite coefficient-envelope demonstration, using exact rational arithmetic.

This executes the finite algorithm in the report. Coverage of an arbitrary
target set is a mathematical premise; a successful execution cannot prove it.
The worked target is X^2+Y^2=1 together with X*Y=0. Its coverage by X and Y
is immediate over Q, and both auxiliaries lie in the degree-1, height-1 box.
"""
from fractions import Fraction as Q
from itertools import product
import json

from plane_intersections import degree2, encode, eval2, intersect


def auxiliary_box(degree_bound, coefficient_height):
    if degree_bound < 1 or coefficient_height < 1:
        return []
    positions = [(i, j) for i in range(degree_bound + 1)
                 for j in range(degree_bound + 1 - i)]
    values = sorted({Q(p, q)
                     for p in range(-coefficient_height, coefficient_height + 1)
                     for q in range(1, coefficient_height + 1)})
    result = []
    for vector in product(values, repeat=len(positions)):
        polynomial = {ij: a for ij, a in zip(positions, vector) if a}
        if degree2(polynomial) > 0:
            result.append(polynomial)
    return result


def envelope_list(f, degree_bound, coefficient_height, accept):
    """Enumerate the finite auxiliary envelope and filter its intersections.

    The report's completeness theorem assumes a nonzero nonconstant f, a fixed
    decidable primitive-recursive predicate accept, and proved coverage by good
    auxiliaries in this box. This callback API does not verify those premises.
    """
    points = set()
    candidates = auxiliary_box(degree_bound, coefficient_height)
    good_count = 0
    for g in candidates:
        result = intersect(f, g)
        if result['status'] == 'success':
            good_count += 1
            points.update(p for p in result['points'] if accept(p))
    points = sorted(points)
    height = max((max(abs(q.numerator), q.denominator)
                  for p in points for q in p), default=0)
    return {'candidates': len(candidates), 'good_candidates': good_count,
            'points': points, 'height': height}


def self_check():
    f = {(2, 0): Q(1), (0, 2): Q(1), (0, 0): Q(-1)}
    result = envelope_list(f, 1, 1, lambda p: p[0] * p[1] == 0)
    expected = [(Q(-1), Q(0)), (Q(0), Q(-1)),
                (Q(0), Q(1)), (Q(1), Q(0))]
    assert result['points'] == expected
    assert result['candidates'] == 24
    assert result['good_candidates'] == 24
    assert all(eval2(f, *p) == 0 for p in result['points'])
    assert result['height'] == 1
    # The complete box contains both explicit auxiliaries used by the proof.
    box = auxiliary_box(1, 1)
    assert {(1, 0): Q(1)} in box and {(0, 1): Q(1)} in box
    return {'status': 'passed', 'scope': 'finite diagnostic, not a universal proof',
            'target': 'X^2+Y^2=1 and X*Y=0',
            'degree_bound': 1, 'coefficient_height': 1,
            'raw_vector_bound': 27, **result}


if __name__ == '__main__':
    print(json.dumps(encode(self_check()), indent=2))
