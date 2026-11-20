"""Exact checks of finite cones on a grid and of the variational certificate."""
from fractions import Fraction as Q
from itertools import combinations, product
from random import Random


def envelope(code, point, slope, metric):
    return min([Q(1)] + [height + slope * metric(point, a) for a, height in code])


def excess(code, f):
    return max([Q(0)] + [f(a) - height for a, height in code])


def code_distance(left, right, slope, metric):
    def value(code, point):
        return envelope(code, point, slope, metric)
    return max(excess(left, lambda x: value(right, x)),
               excess(right, lambda x: value(left, x)))


def optimal(t, x):
    error = (1 - t)**2 / 2
    return error + x**2 - max(Q(0), x - t)**2


def main():
    metric = lambda x, y: abs(x - y)
    nodes = [Q(i, 16) for i in range(17)]
    heights = [Q(i, 4) for i in range(5)]
    rng = Random(19)
    codes = [[]]
    for _ in range(45):
        codes.append([(rng.choice(nodes), rng.choice(heights))
                      for _ in range(rng.randrange(1, 6))])
    count = 0
    for a, b in combinations(codes, 2):
        d = code_distance(a, b, Q(1), metric)
        brute = max(abs(envelope(a, x, Q(1), metric) - envelope(b, x, Q(1), metric))
                    for x in nodes)
        assert d == brute
        count += 1
    print(f"Anchor distance versus exhaustive grid maximum: {count} pairs passed.")
    # A coarse inner net; enumerate all 5^3 entries rather than filtering slopes.
    coarse = [Q(0), Q(1, 2), Q(1)]
    probe = [Q(i, 32) for i in range(33)]
    one_lipschitz = lambda x: Q(1, 2) - abs(x - Q(1, 2))/2
    best_error = Q(1)
    for row in product(heights, repeat=len(coarse)):
        code = list(zip(coarse, row))
        values = [envelope(code, x, Q(1), metric) for x in probe]
        assert all(0 <= y <= 1 for y in values)
        assert all(abs(v-u) <= Q(1, 32) for u,v in zip(values, values[1:]))
        best_error = min(best_error, max(abs(y-one_lipschitz(x)) for x,y in zip(probe,values)))
    print(f"All 125 codes yielded 1-Lipschitz values; best sampled error = {best_error}.")
    for t in nodes:
        err = (1-t)**2 / 2
        values = [optimal(t,x) for x in nodes]
        assert max(abs(y - x*x) for x,y in zip(nodes,values)) == err
        assert all(0 <= y <= 1 for y in values)
        assert all(0 <= v-u <= 2*t*Q(1,16) for u,v in zip(values,values[1:]))
        assert 1-t*t - 2*t*(1-t) == 2*err
    print("Quadratic minimax certificates: 17 slope parameters, both sharpness anchors passed.")


if __name__ == "__main__":
    main()
