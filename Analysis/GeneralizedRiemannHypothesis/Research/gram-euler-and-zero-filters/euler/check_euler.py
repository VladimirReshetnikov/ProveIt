"""Exact integer tests for the leading-digit and conic theorems; standard library."""
import itertools
import json
import math
from collections import Counter
from fractions import Fraction


def directions(p, rank):
    return [v for v in itertools.product(range(p), repeat=rank)
            if next((x for x in v if x), 0) == 1]


def dot(x, v, p):
    return sum(a * b for a, b in zip(x, v)) % p


def disagreement(p, positive, negative):
    rank = len(positive[0])
    mismatches = []
    for v in directions(p, rank):
        left = Counter(dot(x, v, p) for x in positive)
        right = Counter(dot(x, v, p) for x in negative)
        if left != right:
            mismatches.append(v)
    return len(mismatches), str(Fraction((p - 1) * len(mismatches), p ** rank))


def exhaustive_minimum(p, rank, k):
    """Compare every unordered packet pair via exact packed histograms."""
    points = list(itertools.product(range(p), repeat=rank))
    forms = directions(p, rank)
    # Each histogram uses p base-(k+1) digits. Above it is a spare bit.
    # Per-lane OR of the high bit, then minus one, retains that bit
    # precisely if the lane's XOR histogram difference is nonzero.
    lane_width = ((k + 1) ** p - 1).bit_length() + 1
    shifts = [i * lane_width for i in range(len(forms))]
    units = sum(1 << shift for shift in shifts)
    high = units << (lane_width - 1)
    point_codes = [
        sum(((k + 1) ** dot(point, form, p)) << shift
            for form, shift in zip(forms, shifts)) for point in points
    ]
    codes = [sum(packet) for packet in itertools.combinations_with_replacement(point_codes, k)]
    minimum = len(forms)
    histogram = Counter()
    for i, a in enumerate(codes):
        for b in codes[:i]:
            difference = a ^ b
            count = ((((difference | high) - units) & high).bit_count())
            histogram[count] += 1
            minimum = min(minimum, count)
    assert histogram[0] == 0
    assert sum(histogram.values()) == math.comb(len(codes), 2)
    return {'prime': p, 'rank': rank, 'mass': k, 'directions_minimum': minimum,
            'pairs': sum(histogram.values()), 'spectrum_counts': dict(sorted(histogram.items()))}


def norm_one_packets(p):
    """Division into the two square classes on x^2-n y^2=1, n nonsquare."""
    n = next(x for x in range(2, p) if pow(x, (p - 1) // 2, p) == p - 1)
    torus = {(x, y) for x, y in itertools.product(range(p), repeat=2)
             if (x*x - n*y*y) % p == 1}
    squares = {((x*x + n*y*y) % p, 2*x*y % p) for x, y in torus}
    assert len(torus) == p + 1 and len(squares) == (p + 1) // 2
    return sorted(squares), sorted(torus - squares)


def sextic_line_test():
    representatives = [('1', lambda t: 1), ('t', lambda t: t),
                       ('t^2', lambda t: t*t), ('t^2-1', lambda t: t*t-1),
                       ('t^2-2', lambda t: t*t-2)]
    rows = []
    for label, quadratic in representatives:
        nodes = [t for t in range(11) if quadratic(t) % 11]
        tested = 0
        for subset in itertools.combinations(nodes, 6):
            tested += 1
            squares = {(quadratic(t) * math.prod(t-u for u in subset if u != t))**2 % 11
                       for t in subset}
            assert len(squares) > 1
        rows.append({'quadratic': label, 'tested': tested, 'passing': 0})
    return rows


def main():
    planar = exhaustive_minimum(3, 2, 1)
    lifted = exhaustive_minimum(3, 3, 3)
    assert planar['directions_minimum'] == lifted['directions_minimum'] == 3
    constructions = []
    for p in (7, 11, 13, 17, 19, 23, 29, 31):
        positive, negative = norm_one_packets(p)
        number, density = disagreement(p, positive, negative)
        assert number == (p + 1) // 2
        constructions.append({'prime': p, 'rank': 2, 'reduced_mass': len(positive),
                              'directions': number, 'disagreement': density})
        if p in (7, 11, 13):
            # Pull back to dimension three along the quotient forgetting z.
            a3 = [x + (z,) for x in positive for z in range(p)]
            c3 = [x + (z,) for x in negative for z in range(p)]
            number3, density3 = disagreement(p, a3, c3)
            assert number3 == number and Fraction(density3) * p == Fraction(density)
            constructions.append({'prime': p, 'rank': 3, 'reduced_mass': len(a3),
                                  'directions': number3, 'disagreement': density3})
    positive = [(1, 0), (10, 0), (5, 3), (5, 8), (6, 3), (6, 8)]
    negative = [(0, 1), (0, 10), (3, 5), (3, 6), (8, 5), (8, 6)]
    for side in (positive, negative):
        side.extend([(0, 0), (0, 0)])
    matches = [list(v) for v in directions(11, 2)
               if Counter(dot(x, v, 11) for x in positive)
               == Counter(dot(x, v, 11) for x in negative)]
    assert matches == [[1, t] for t in (1, 3, 4, 7, 8, 10)]
    assert disagreement(11, positive, negative) == (6, '60/121')
    print(json.dumps({'exhaustive': [planar, lifted], 'attaining_examples': constructions,
                      'eleven_size_eight_matching_directions': matches,
                      'eleven_sextic_line_obstruction': sextic_line_test()}, indent=2))


if __name__ == '__main__':
    main()
