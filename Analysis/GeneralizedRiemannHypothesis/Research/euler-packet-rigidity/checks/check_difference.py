"""Check the flat-difference cycle bound on exact rank-three examples."""
from itertools import product


def translate(point, direction, scale, p):
    return tuple((x + scale * y) % p for x, y in zip(point, direction))


def check_case(p, dimension, separation):
    points = list(product(range(p), repeat=3))
    zero = (0, 0, 0)
    t = (1, 1, 1)
    base = (1, 0, 1)
    d1 = (2, 1, 0)
    d2 = (1, 0, 0)
    values = dict.fromkeys(points, 0)
    first_flat = set()
    expected_positive_lines = 0
    for i in range(p):
        for j in range(p if dimension == 2 else 1):
            start = translate(translate(base, d1, i, p), d2, j, p)
            first_flat.add(start)
            # A parabola on the two-dimensional flat breaks translation periods.
            layer = i if dimension == 1 else (j - i * i) % p
            positive = layer < p - separation
            expected_positive_lines += positive
            for step in range(p):
                point = translate(start, t, step, p)
                values[point] = int(step < separation) - int(not positive)

    second_flat = {translate(x, t, separation, p) for x in first_flat}
    delta = {x: values[x] - values[translate(x, t, -1, p)] for x in points}
    assert set(delta.values()) <= {-1, 0, 1}
    assert {x for x in points if delta[x] == 1} == first_flat
    assert {x for x in points if delta[x] == -1} == second_flat
    assert first_flat.isdisjoint(second_flat)
    plus = {x for x in points if values[x] == 1}
    minus = {x for x in points if values[x] == -1}
    assert len(plus) == len(minus)
    # On reversing signs if necessary, t occurs as a difference y-a in the packet.
    assert any(translate(x, t, 1, p) in side for side in (plus, minus) for x in side)
    periods = {u for u in points
               if all(values[translate(x, u, 1, p)] == value
                      for x, value in values.items())}
    assert periods == {zero}

    # Recover each quotient fiber by subtracting its last coordinate times t.
    def project(x):
        return translate(x, t, -x[2], p)[:2]

    assert {project(x) for x in first_flat} == {project(x) for x in second_flat}
    size = len(first_flat)
    assert len({project(x) for x in first_flat}) == size == p ** dimension
    positive_lines = negative_lines = 0
    for u, v in product(range(p), repeat=2):
        fiber = [translate((u, v, 0), t, step, p) for step in range(p)]
        assert sum(delta[x] for x in fiber) == 0
        jumps = [index for index, x in enumerate(fiber) if delta[x] == 1]
        if not jumps:
            assert all(delta[x] == 0 for x in fiber)
            continue
        assert len(jumps) == 1
        assert delta[fiber[(jumps[0] + separation) % p]] == -1
        signs = [values[x] for x in fiber]
        if 1 in signs:
            assert signs.count(1) == separation and -1 not in signs
            positive_lines += 1
        else:
            assert signs.count(-1) == p - separation and 1 not in signs
            negative_lines += 1
    assert positive_lines == expected_positive_lines
    assert positive_lines + negative_lines == size
    mass = len(plus)
    assert mass >= max(positive_lines * separation, negative_lines * (p - separation))
    assert p * mass >= size * separation * (p - separation) >= size * (p - 1)
    # The construction attains the sharper first bound for every separation.
    assert p * mass == size * separation * (p - separation)
    assert (p * mass == size * (p - 1)) == (separation in (1, p - 1))

    # Direct projected multiplicities also test the derivative support identity.
    def trace_differs(table, v):
        counts = [0] * p
        for x, value in table:
            counts[sum(a * b for a, b in zip(x, v)) % p] += value
        return any(counts)
    rows = [(x, value) for x, value in values.items() if value]
    derivative_rows = [(x, value) for x, value in delta.items() if value]
    for v in points:
        assert trace_differs(derivative_rows, v) == (
            sum(v) % p != 0 and trace_differs(rows, v)
        )
    return mass, size, positive_lines, negative_lines


if __name__ == '__main__':
    total = 0
    for prime in (3, 5, 7):
        for flat_dimension in (1, 2):
            results = [check_case(prime, flat_dimension, s)
                       for s in range(1, prime)]
            mass, size, pos, neg = results[0]
            print(f"p={prime}, flat size {size}: all {prime-1} separations checked; "
                  f"at s=1 mass {mass}, positive/negative cycles {pos}/{neg}.")
            total += len(results)
    print(f"All {total} rank-three constructions passed.")
