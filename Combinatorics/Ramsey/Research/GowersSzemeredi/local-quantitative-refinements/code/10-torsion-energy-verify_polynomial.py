#!/usr/bin/env python3
"""Exact verification of the displayed F_5^4 polynomial coloring.

No external packages are required.  This finite check supplements the
general proof; it is not used to infer the general dimension theorem.
"""

from itertools import product
import json


P = 5


def cubic_norm(a, b, c):
    return (
        a**3 - 2*a*a*c + a*c*c + a*b*b + 3*a*b*c
        - b**3 - b*c*c + c**3
    ) % P


def multiplication_determinant(a, b, c):
    # Columns are multiplication by a+b*theta+c*theta^2 on 1, theta,
    # theta^2, where theta^3+theta+1=0.
    matrix = ((a, -c, -b), (b, a-c, -b-c), (c, b, a-c))
    u, v, w = matrix
    return (
        u[0]*(v[1]*w[2] - v[2]*w[1])
        - u[1]*(v[0]*w[2] - v[2]*w[0])
        + u[2]*(v[0]*w[1] - v[1]*w[0])
    ) % P


def main():
    roots = [t for t in range(P) if (t**3 + t + 1) % P == 0]
    assert not roots, "The defining cubic must be irreducible."
    triples = list(product(range(P), repeat=3))
    for triple in triples:
        assert cubic_norm(*triple) == multiplication_determinant(*triple)
    norm_zeros = [t for t in triples if cubic_norm(*t) == 0]
    assert norm_zeros == [(0, 0, 0)]

    vectors = list(product(range(P), repeat=4))
    colors = {v: (v[0] + cubic_norm(*v[1:])) % P for v in vectors}
    sizes = [sum(color == i for color in colors.values()) for i in range(P)]
    assert sizes == [125] * P
    zero = (0, 0, 0, 0)
    directions = [h for h in vectors if h != zero]
    checked = 0
    for a in vectors:
        for h in directions:
            progression = [
                tuple((a[j] + i*h[j]) % P for j in range(4))
                for i in range(4)
            ]
            assert len(set(progression)) == 4
            assert not (
                colors[progression[0]] == colors[progression[3]]
                and colors[progression[1]] == colors[progression[2]]
            ), (a, h, progression)
            checked += 1
    assert checked == 390000
    print(json.dumps({
        "prime": P,
        "defining_cubic": "T^3+T+1",
        "irreducible_cubic": True,
        "determinant_evaluations_checked": len(triples),
        "norm_zero_count": len(norm_zeros),
        "color_class_sizes": sizes,
        "ordered_nontrivial_4aps_checked": checked,
        "symmetric_4aps_found": 0,
        "status": "PASS",
    }, indent=2))


if __name__ == "__main__":
    main()
