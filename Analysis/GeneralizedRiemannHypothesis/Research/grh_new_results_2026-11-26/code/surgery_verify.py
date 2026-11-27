#!/usr/bin/env python3
"""Exact finite algebra for the worked all-real zero surgery example.

No third-party dependencies. The infinite product is sin(pi*t)/(pi*t).
All certified assertions use fractions.Fraction; decimals are illustrative.
The polynomial variable below is x=t**2.
"""

from decimal import Decimal, localcontext
from fractions import Fraction as Q
import json


def multiply(p, q):
    result = [Q(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            result[i + j] += a * b
    return result


def factors(nodes):
    result = [Q(1)]
    for a in nodes:
        result = multiply(result, [Q(1), -a])
    return result


def main():
    anchors = [Q(1), Q(1, 4)]
    removed = [Q(1, 100), Q(1, 121)]
    target = Q(4, 625)  # T = 25/2, which is not a zero of sin(pi*t)/(pi*t).
    multiplicity = 2
    q1, q2 = [
        sum(a**k for a in anchors)
        + sum(b**k for b in removed)
        - multiplicity * target**k
        for k in (1, 2)
    ]
    e2 = (q1**2 - q2) / 2
    discriminant = q1**2 - 4 * e2
    assert discriminant > 0 and q1 > 0 and e2 > 0
    # Hence the two real roots have positive sum and positive product.
    polynomial = lambda u: u**2 - q1 * u + e2
    intervals = [(Q(99, 100), Q(101, 100)), (Q(6, 25), Q(27, 100))]
    brackets = []
    for left, right in intervals:
        pl, pr = polynomial(left), polynomial(right)
        assert left > 0 and pl * pr < 0
        brackets.append({
            "left": str(left), "right": str(right),
            "P_left": str(pl), "P_right": str(pr),
        })
    assert intervals[1][1] < intervals[0][0]

    numerator = multiply([Q(1), -q1, e2], factors([target] * multiplicity))
    denominator = factors(anchors + removed)
    difference = [a - b for a, b in zip(numerator, denominator)]
    assert difference[:3] == [0, 0, 0]
    assert difference[3] != 0
    # Thus numerator - denominator is exactly divisible by x^3=t^6,
    # which certifies matching Taylor derivatives through order five.

    with localcontext() as ctx:
        ctx.prec = 60
        dec = lambda v: Decimal(v.numerator) / Decimal(v.denominator)
        root_disc = dec(discriminant).sqrt()
        roots = [(dec(q1) + root_disc) / 2, (dec(q1) - root_disc) / 2]
        ordinates = [Decimal(1) / u.sqrt() for u in roots]
        print(json.dumps({
            "status": "all exact rational assertions passed",
            "model": "sin(pi*t)/(pi*t)",
            "matched_derivative_orders": "0 through 5",
            "new_double_zeros": ["25/2", "-25/2"],
            "anchor_nodes": [str(a) for a in anchors],
            "removed_nodes": [str(b) for b in removed],
            "target_node": str(target),
            "q1": str(q1), "q2": str(q2), "e2": str(e2),
            "discriminant": str(discriminant),
            "root_brackets": brackets,
            "new_nodes_approximate": [str(u) for u in roots],
            "new_ordinates_approximate": [str(v) for v in ordinates],
            "numerator_coefficients_ascending_in_t_squared": [str(v) for v in numerator],
            "denominator_coefficients_ascending_in_t_squared": [str(v) for v in denominator],
            "difference_coefficients_ascending_in_t_squared": [str(v) for v in difference],
            "eventual_zero_count": "N_G(Y) = floor(Y) for Y >= 25/2",
        }, indent=2))


if __name__ == "__main__":
    main()
