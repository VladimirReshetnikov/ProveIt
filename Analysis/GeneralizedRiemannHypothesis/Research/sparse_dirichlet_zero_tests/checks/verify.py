#!/usr/bin/env python3
"""Verify the finite lemmas and the quadratic example using exact arithmetic."""

from fractions import Fraction as Q
from itertools import combinations
from math import comb


ALLOWED = frozenset(map(Q, ("4/3", "3/2", "2", "3", "4")))
MODEL = tuple(map(Q, (-3, -1, 0, 1, 3)))


def subsets(points):
    for size in range(len(points) + 1):
        yield from combinations(points, size)


def normalize(points):
    """Send the least and greatest entries of an ordered set to 0 and 1."""
    lo, hi = points[0], points[-1]
    return tuple((x - lo) / (hi - lo) for x in points)


def triple_ratio(a, b, c):
    return (c - a) / (b - a)


def cross_ratio(a, b, c, d):
    return (c - a) * (d - b) / ((c - b) * (d - a))


def passes(points):
    return (all(triple_ratio(*triple) in ALLOWED
                for triple in combinations(points, 3))
            and all(cross_ratio(*quad) in ALLOWED
                    for quad in combinations(points, 4)))


def display(points):
    return "{" + ", ".join(map(str, points)) + "}"


def verify_configurations():
    candidates = tuple(sorted(1 / ratio for ratio in ALLOWED))
    assert candidates == tuple(map(Q, ("1/4", "1/3", "1/2", "2/3", "3/4")))
    admissible = set()
    for interior in subsets(candidates):
        points = (Q(0), *interior, Q(1))
        if passes(points):
            admissible.add(points)
    model_shapes = {normalize(points) for points in subsets(MODEL)
                    if len(points) >= 2}
    assert admissible == model_shapes
    maximal = sorted(points for points in admissible
                     if not any(set(points) < set(other) for other in admissible))
    expected_interiors = {tuple(map(Q, values)) for values in [
        ("1/4", "1/2"), ("1/3", "1/2", "2/3"), ("1/2", "3/4")]}
    assert {points[1:-1] for points in maximal} == expected_interiors
    # A non-affine projective constraint really is used. These four
    # pass their triple tests and fail the cross ratio.
    example = tuple(map(Q, ("0", "1/4", "3/4", "1")))
    assert all(triple_ratio(*triple) in ALLOWED
               for triple in combinations(example, 3))
    assert cross_ratio(*example) == Q(9, 8)
    print(f"Normalized interior candidates: {display(candidates)}")
    print(f"Admissible normalized configurations: {len(admissible)} of "
          f"{2**len(candidates)} subsets tested")
    for points in maximal:
        preimage = next(source for source in subsets(MODEL)
                        if len(source) >= 2 and normalize(source) == points)
        print(f"  {display(points)} from {display(preimage)}")
    print("Cross-ratio obstruction for {0, 1/4, 3/4, 1}: 9/8")


def sixth_power_in_quadratic_field(x, y):
    """Return rational coefficients of (x + y sqrt(-3))**6."""
    real, imag = Q(0), Q(0)
    for j in range(7):
        term = comb(6, j) * x ** (6-j) * y ** j * (-3) ** (j//2)
        if j % 2:
            imag += term
        else:
            real += term
    return real, imag


def verify_model_witness():
    # For gamma = sqrt(-3), (gamma-c)^(-1) = (-c-sqrt(-3))/(c^2+3).
    print("Nodes (sqrt(-3)-c)^(-6) on the five-point model:")
    for c in MODEL:
        norm = c*c + 3
        real, imag = sixth_power_in_quadratic_field(-c / norm, -1 / norm)
        assert imag == 0 and real != 0
        print(f"  c={c}: {real}")


def power_sums(c, max_power):
    """Compute sum (gamma-c)^(-k) for roots of 3z^2-3z+1, 0 <= k <= max_power."""
    f = 3*c*c - 3*c + 1
    derivative = 6*c - 3
    root_sum = Q(-derivative, f)
    root_product = Q(3, f)
    moments = [Q(2), root_sum]
    for _ in range(2, max_power + 1):
        moments.append(root_sum * moments[-1] - root_product * moments[-2])
    # Independently evaluate [t^j] -F'(c+t)/F(c+t) by series division.
    # This checks that the logarithmic-derivative sign and Taylor index agree.
    coefficients = []
    for j in range(max_power):
        numerator = -derivative if j == 0 else -6 if j == 1 else 0
        if j >= 1:
            numerator -= derivative * coefficients[j-1]
        if j >= 2:
            numerator -= 3 * coefficients[j-2]
        coefficients.append(Q(numerator, f))
    assert coefficients == moments[1:]
    return moments


def verify_quadratic_example():
    print("F(z)=3z^2-3z+1; p_j=sum (gamma-c)^(-j):")
    for c in (0, 1, 5):
        moments = power_sums(c, 24)
        # gamma = (3+sqrt(-3))/6. This verifies p_6 separately in Q(sqrt(-3)).
        a = 3-6*c
        norm = a*a + 3
        real, imag = sixth_power_in_quadratic_field(Q(6*a, norm), Q(-6, norm))
        assert moments[6] == 2*real
        assert (imag == 0) == (c in (0, 1))
        d0 = moments[0] * moments[12] - moments[6]**2
        d2 = moments[12] * moments[24] - moments[18]**2
        assert d0 == -12 * imag**2
        assert d2 == d0 * (real**2 + 3*imag**2)**2
        if c == 5:
            assert d2 == Q(-11226235159675972800, 61**24)
        else:
            assert real == -27 and d0 == d2 == 0
        print(f"  c={c}: p_6={moments[6]}, det(H_0)={d0}, det(H_2)={d2}")


def field_product(left, right):
    """Multiply coefficient pairs in Q(sqrt(-3))."""
    a, b = left
    c, d = right
    return a*c - 3*b*d, a*d + b*c


def field_power(z, exponent):
    value = (Q(1), Q(0))
    for _ in range(exponent):
        value = field_product(value, z)
    return value


def node(root, center):
    """Sixth inverse power of (root - center), including its phase."""
    a, b = root[0] - center, root[1]
    norm = a*a + 3*b*b
    return field_power((Q(a, norm), Q(-b, norm)), 6)


def matrix_inertia(matrix):
    """Count positive, negative and zero squares by exact symmetric elimination."""
    form = [row[:] for row in matrix]
    positive = negative = 0
    while form:
        size = len(form)
        piv = next((i for i in range(size) if form[i][i]), None)
        if piv is None:
            pair = next(((i, j) for i in range(size) for j in range(i+1, size)
                         if form[i][j]), None)
            if pair is None:
                return positive, negative, size
            # Replace basis vector e_i by e_i+e_j. The diagonal was zero,
            # so the new i-th diagonal is twice the nonzero off-diagonal.
            i, j = pair
            for k in range(size):
                form[i][k] += form[j][k]
            for k in range(size):
                form[k][i] += form[k][j]
            piv = i
        diagonal = form[piv][piv]
        positive += (diagonal > 0)
        negative += (diagonal < 0)
        keep = [i for i in range(size) if i != piv]
        form = [[form[i][j] - form[i][piv]*form[piv][j]/diagonal
                 for j in keep] for i in keep]
    return positive, negative, 0


def shifted_window(nodes, shift, size):
    powers = []
    for k in range(shift, shift + 2*size - 1):
        terms = [field_power(z, k) for z in nodes]
        assert sum(b for _, b in terms) == 0
        powers.append(sum(a for a, _ in terms))
    return [[powers[i+j] for j in range(size)] for i in range(size)]


def verify_collision_and_inertia():
    # Two distinct off-axis conjugate pairs. The first has multiplicity two.
    # There are also two distinct real zeros. The maximal window ranks are
    # determined by distinct image nodes rather than these multiplicities.
    roots = [(0, 0), (1, 0), (10, 1), (10, -1), (10, 1), (10, -1),
             (20, 1), (20, -1)]
    blind_sets = [{u + offset for offset in (-3, -1, 0, 1, 3)} for u in (10, 20)]
    critical = blind_sets[0] | blind_sets[1] | {15}
    assert len(critical) == 11
    left, right = node((10, 1), 15), node((20, 1), 15)
    assert left == (right[0], -right[1]) and left[1] != 0
    # Exercise both the off-diagonal pivot and the null termination.
    assert matrix_inertia([[Q(0), Q(1), Q(0)], [Q(1), Q(0), Q(0)],
                           [Q(0), Q(0), Q(0)]]) == (1, 1, 1)
    deficit = 0
    print("Two-pair collision example, window dimension 7, shifts 2, 8, 16:")
    for c in sorted(critical | {5}):
        nodes = [node(root, c) for root in roots]
        distinct = set(nodes)
        real_count = sum(b == 0 for _, b in distinct)
        nonreal_pairs = sum(b > 0 for _, b in distinct)
        assert len(distinct) == real_count + 2*nonreal_pairs
        expected = (real_count + nonreal_pairs, nonreal_pairs, 7-len(distinct))
        for shift in (2, 8, 16):
            assert matrix_inertia(shifted_window(nodes, shift, 7)) == expected
        loss = 2 - nonreal_pairs
        assert loss == int(c in critical)
        deficit += loss
        print(f"  c={c}: inertia {expected}, deficit {loss}")
    assert deficit == 5*2 + comb(2, 2)
    print(f"Total deficit {deficit} = 5D + binom(D,2) for D=2.")


if __name__ == "__main__":
    verify_configurations()
    verify_model_witness()
    verify_quadratic_example()
    verify_collision_and_inertia()
    print("All exact checks passed.")
