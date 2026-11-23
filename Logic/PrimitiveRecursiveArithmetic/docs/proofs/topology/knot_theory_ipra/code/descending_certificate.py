"""Descending diagram certificates with exact rational triangle-move replay.

Input to strip_certificate is the based planar traversal b, b+, ..., b-, b
from the paper. Points may use integers or fractions.Fraction. The original
diagram is obtained by joining b- directly to b+ in its regular base edge.
"""

from fractions import Fraction as Q
from itertools import permutations


def first_under(visits):
    seen, change = set(), set()
    for visit in visits:
        if visit < 0 and -visit not in seen:
            change.add(-visit)
        seen.add(abs(visit))
    return change


def warping(visits):
    """First-under minima for both directions, plus a cheapest change set."""
    if not visits:
        return 0, 0, set()
    assert len(set(visits)) == len(visits) and set(visits) == {-v for v in visits}
    assert 0 not in visits
    best = []
    for word in [visits, visits[::-1]]:
        sets = (first_under(word[j:] + word[:j]) for j in range(len(word)))
        best.append(min(sets, key=len))
    return len(best[0]), len(best[1]), min(best, key=len)


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def cross(a, b):
    x, y, z = a
    u, v, w = b
    return y * w - z * v, z * u - x * w, x * v - y * u


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def intersection_interval(tri, start, end):
    """Parameter interval where a closed segment lies in a closed triangle."""
    a, b, c = tri
    normal = cross(sub(b, a), sub(c, a))
    assert any(normal)
    heights = [dot(normal, sub(p, a)) for p in (start, end)]
    lo, hi = Q(0), Q(1)
    if heights[0] == heights[1]:
        if heights[0]:
            return None
    else:
        lo = hi = Q(-heights[0], heights[1] - heights[0])
        if not 0 <= lo <= 1:
            return None
    for u, v in ((a, b), (b, c), (c, a)):
        direction = sub(v, u)
        f, g = [dot(normal, cross(direction, sub(p, u))) for p in (start, end)]
        if f == g:
            if f < 0:
                return None
        elif g > f:
            lo = max(lo, Q(-f, g - f))
        else:
            hi = min(hi, Q(-f, g - f))
    return (lo, hi) if lo <= hi else None


def strip_certificate(points):
    points = [tuple(map(Q, p)) for p in points]
    m = len(points) - 1
    b = points[0]
    assert b == points[-1] and b not in points[1:-1] and m >= 4
    chain = [(*p, Q(m - i)) for i, p in enumerate(points)]
    spine = [(*b, Q(m - i)) for i in range(m + 1)]
    start = chain[1:-1]
    moves = [("insert", chain[-2], chain[0], chain[1]),
             ("insert", chain[-2], chain[-1], chain[0])]
    for j in range(m - 1, 0, -1):
        moves.append(("subdivide", spine[j + 1], spine[j], spine[0]))
    moves.append(("delete", spine[1], chain[0], chain[1]))
    for j in range(1, m - 1):
        moves.append(("delete", spine[j], chain[j], chain[j + 1]))
        moves.append(("delete", spine[j + 1], spine[j], chain[j + 1]))
    return start, moves


def replay(initial, moves):
    """Check all arc incidences and all intersections with untouched edges."""
    cycle = list(initial)
    for kind, u, point, v in moves:
        i = cycle.index(u)
        cycle = cycle[i:] + cycle[:i]
        deleting = kind == "delete"
        if deleting:
            assert cycle[1:3] == [point, v]
        else:
            assert kind in ("insert", "subdivide") and cycle[1] == v
        if kind == "subdivide":
            assert not any(cross(sub(point, u), sub(v, u)))
            assert dot(sub(point, u), sub(point, v)) < 0
        else:
            tri = (u, point, v)
            assert any(cross(sub(point, u), sub(v, u)))
            for j in range(2 if deleting else 1, len(cycle)):
                a, b = cycle[j], cycle[(j + 1) % len(cycle)]
                hit = intersection_interval(tri, a, b)
                if hit is not None:
                    lo, hi = hit
                    assert lo == hi and ((lo == 0 and a in (u, v)) or
                                         (lo == 1 and b in (u, v)))
        if deleting:
            del cycle[1]
        else:
            cycle.insert(1, point)
    assert len(cycle) == 3
    assert any(cross(sub(cycle[1], cycle[0]), sub(cycle[2], cycle[0])))
    return cycle


def main():
    cases = 0
    for c in range(1, 5):
        visits = list(range(1, c + 1)) + list(range(-c, 0))
        # Rotate the single positive visit numbered 1 to the front.
        for tail in permutations(v for v in visits if v != 1):
            word = (1,) + tail
            forward, reverse, changed = warping(word)
            alternating = all(x * y < 0 for x, y in zip(word, word[1:] + word[:1]))
            assert forward + reverse <= c - 1
            assert (forward + reverse == c - 1) == alternating
            assert len(changed) <= (c - 1) // 2
            cases += 1
    walks = [
        [(0, 0), (1, 0), (3, 0), (4, 3), (-3, 3), (-3, 0), (-1, 0), (0, 0)],
        [(0, 0), (1, 0), (3, 0), (-3, 4), (3, 4), (-3, 0), (-1, 0), (0, 0)],
        [(0, 0), (1, 0), (3, 0), (-3, 4), (3, 2), (-1, -4),
         (-4, 2), (-3, 0), (-1, 0), (0, 0)],
    ]
    steps = 0
    for walk in walks:
        for oriented in (walk, walk[::-1]):
            start, moves = strip_certificate(oriented)
            replay(start, moves)
            steps += len(moves)
    print(f"Verified {cases} signed visit words and {steps} exact spatial move steps.")


if __name__ == "__main__":
    main()
