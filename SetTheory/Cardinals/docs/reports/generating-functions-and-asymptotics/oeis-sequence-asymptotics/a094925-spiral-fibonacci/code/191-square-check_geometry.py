"""Independent step-generated geometry, exact squared Euclidean distances.

The path and selected neighbor are generated without the closed index formula.
The finite checks supplement the all-index occupied-rectangle proof.
"""
from math import isqrt
from spiral import MAX_INDEX, integer, predecessor, quarter

OUTGOING = ((0, -1), (1, 0), (0, 1), (-1, 0))
SHELLS = (
    (1, ((1, 0), (-1, 0), (0, 1), (0, -1))),
    (2, ((1, 1), (1, -1), (-1, 1), (-1, -1))),
)


def need(condition, message):
    if not condition:
        raise ValueError('geometry: ' + str(message))


def spiral_points(last):
    integer(last, 0, MAX_INDEX, 'last index')
    x = y = n = 0
    yield (x, y)
    directions = ((1, 0), (0, 1), (-1, 0), (0, -1))
    length, direction = 1, 0
    while n < last:
        for _ in range(2):
            dx, dy = directions[direction % 4]
            for _ in range(length):
                if n == last:
                    return
                x, y, n = x + dx, y + dy, n + 1
                yield (x, y)
            direction += 1
        length += 1


def corner_point(k):
    integer(k, 2, 2 * MAX_INDEX + 2, 'corner index')
    m, residue = divmod(k, 4)
    return ((-m, m), (-m, -m), (m + 1, -m), (m + 1, m + 1))[residue]


def nearest_earlier_nonpredecessor(point, seen, n):
    """Search exact lattice shells; absence and ties are explicit failures.

    No positive integer squared distance falls strictly between 0, 1, and 2.
    A located shell therefore gives a global nearest point, not a heuristic.
    """
    x, y = point
    for distance, offsets in SHELLS:
        candidates = []
        for dx, dy in offsets:
            index = seen.get((x + dx, y + dy))
            if index is not None and index != n - 1:
                candidates.append(index)
        if candidates:
            return distance, sorted(candidates)
    raise ValueError('no eligible earlier neighbor within squared distance 2')


def run_checks(listed, limit=250000, brute_limit=4096):
    integer(limit, 63, MAX_INDEX, 'geometry limit')
    integer(brute_limit, 8, limit, 'brute-force limit')
    need(type(listed) is list and len(listed) == 64
         and all(type(v) is int and v >= 0 for v in listed), '64 nonnegative integer fixture terms')
    points, geometric_t, seen = [], [0], {}
    corner_count = rectangle_count = 0
    for n, point in enumerate(spiral_points(limit)):
        points.append(point)
        if n >= 1:
            k = isqrt(4*n + 1)
            q, length = quarter(k), (k + 1) // 2
            j = n - q
            need(q <= n < quarter(k+1) and 0 <= j < length, ('corner interval', n))
            cx, cy = corner_point(k)
            ux, uy = OUTGOING[k % 4]
            need(point == (cx+j*ux, cy+j*uy), ('coordinate formula', n))
            if j == 0:
                corner_count += 1
                if n <= brute_limit:
                    wx, wy = OUTGOING[(k-1) % 4]
                    rectangle = {(cx+a*wx+b*ux, cy+a*wy+b*uy)
                                 for a in range(-(k//2), 0) for b in range(length)}
                    need(rectangle == set(seen), ('complete occupied rectangle', n))
                    rectangle_count += 1
        if n >= 2:
            distance, candidates = nearest_earlier_nonpredecessor(point, seen, n)
            need(len(candidates) == 1, ('uniqueness', n))
            actual = candidates[0]
            geometric_t.append(actual)
            need(actual == predecessor(n), ('closed predecessor formula', n))
            need(distance == (2 if n == q else 1), ('distance class', n))
            if n <= brute_limit:
                distances = [(point[0]-earlier[0])**2 + (point[1]-earlier[1])**2
                             for earlier in points[:n-1]]
                minimum = min(distances)
                brute = [i for i, d in enumerate(distances) if d == minimum]
                need(minimum == distance and brute == candidates, ('global brute force', n))
        elif n == 1:
            geometric_t.append(0)
        need(point not in seen, ('self intersection', n))
        seen[point] = n
    sequence = [0, 1]
    for n in range(2, len(listed)):
        sequence.append(sequence[-1] + sequence[geometric_t[n]])
    need(sequence == listed, 'all listed OEIS values')
    need(all(geometric_t[n] - geometric_t[n-1] in (0, 1)
             for n in range(2, limit+1)), 'nondecreasing unit increments')
    need(all(predecessor(n) == 0 for n in range(2, 8)), 'initial zero plateau')
    return {'generated_indices': [0, limit],
            'unique_nearest_nonpredecessor_indices': [2, limit],
            'global_bruteforce_indices': [2, brute_limit],
            'coordinate_formula_indices': [1, limit],
            'corner_coordinates_checked': corner_count,
            'complete_precorner_rectangles_checked': rectangle_count,
            'listed_OEIS_terms_matched': len(listed),
            'listed_OEIS_index_range': [0, len(listed)-1],
            'last_listed_term': listed[-1],
            'first_24_predecessors': geometric_t[:24],
            'metric': 'Euclidean distance between lattice cell centers',
            'ties_after_excluding_immediate_predecessor': 0}
