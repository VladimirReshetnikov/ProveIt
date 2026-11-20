"""Exact conversion from a ramp-expectation oracle, sparse couplings and dual tests.

Run as a script with Python >= 3.9. Fractions are used for every numerical
assertion. The test oracle is a mixture of Lebesgue measure and rational atoms.
"""
from fractions import Fraction as Q
from random import Random


def checked(law):
    assert law and sum(m for _, m in law) == 1
    assert all(0 <= x <= 1 and m > 0 for x, m in law)
    assert all(a[0] < b[0] for a, b in zip(law, law[1:]))
    return law


def reconstruct(n, r, read):
    N = 2**n
    level, law, repairs = Q(0), [], 0
    for i in range(N):
        raw = read(i, n, r)
        clipped = min(Q(1), max(Q(0), raw))
        new = max(level, clipped)
        repairs += clipped < level
        if new > level:
            law.append((Q(i, N), new - level))
        level = new
    if level < 1:
        law.append((Q(1), 1 - level))
    return checked(law), repairs


def sparse_coupling(p, q):
    i = j = 0
    a, b = p[0][1], q[0][1]
    joint = []
    while i < len(p) and j < len(q):
        t = min(a, b)
        joint.append((p[i][0], q[j][0], t))
        a, b = a - t, b - t
        if a == 0:
            i += 1
            if i < len(p):
                a = p[i][1]
        if b == 0:
            j += 1
            if j < len(q):
                b = q[j][1]
    assert i == len(p) and j == len(q)
    return joint


def certificate(p, q):
    sites = sorted({Q(0), Q(1), *(x for x, _ in p), *(x for x, _ in q)})
    P, R = dict(p), dict(q)
    potential, cost, flow = {sites[0]: Q(0)}, Q(0), Q(0)
    for x, y in zip(sites, sites[1:]):
        flow += P.get(x, 0) - R.get(x, 0)
        width = y - x
        cost += abs(flow) * width
        potential[y] = potential[x] - (width if flow >= 0 else -width)
    joint = sparse_coupling(p, q)
    left, right = {}, {}
    for x, y, m in joint:
        left[x] = left.get(x, 0) + m
        right[y] = right.get(y, 0) + m
    assert left == P and right == R
    assert len(joint) <= len(p) + len(q) - 1
    assert sum(abs(x-y)*m for x, y, m in joint) == cost
    assert sum((P.get(x, 0) - R.get(x, 0))*v for x, v in potential.items()) == cost
    return cost, len(joint)


# The test measure has density 1/4 and three atoms. It charges 0 and 1.
DENSITY = Q(1, 4)
ATOMS = [(Q(0), Q(1, 7)), (Q(3, 7), Q(1, 4)), (Q(1), Q(5, 14))]


def true_ramp(i, n):
    size = 2**n
    lower, upper = Q(i, size), Q(i+1, size)
    area = (lower + upper) / 2
    def at(x):
        return min(Q(1), max(Q(0), (upper - x)*size))
    return DENSITY*area + sum(m*at(x) for x, m in ATOMS)


def read(i, n, r):
    # Adversarial alternating signed error can reverse successive readings.
    return true_ramp(i, n) + Q(1 if i % 2 == 0 else -1, 2**r)


def true_cost(law):
    # Integrate |CDF_target - CDF_law| exactly by splitting affine segments
    # at atoms and, when needed, at a zero of the difference.
    points = sorted({Q(0), Q(1), *(x for x, _ in law), *(x for x, _ in ATOMS)})
    result = Q(0)
    for x, y in zip(points, points[1:]):
        jump = sum(m for z, m in ATOMS if z <= x) - sum(m for z, m in law if z <= x)
        a, b = DENSITY*x + jump, DENSITY*y + jump
        if a*b < 0:
            result += (a*a+b*b)/(2*DENSITY)
        else:
            result += (abs(a)+abs(b))*(y-x)/2
    return result


def random_law(rng):
    pts = sorted(rng.sample(range(33), rng.randrange(1, 12)))
    nums = [rng.randrange(1, 15) for _ in pts]
    return checked([(Q(x, 32), Q(m, sum(nums))) for x, m in zip(pts, nums)])


def main():
    assert DENSITY + sum(m for _, m in ATOMS) == 1
    print("level  sites  monotone repairs  exact W to mixture  theorem bound")
    laws = []
    for p in range(7):
        n = r = p + 2
        law, repaired = reconstruct(n, r, read)
        err, bound = true_cost(law), Q(1, 2**(n+1)) + Q(1, 2**r)
        assert err <= bound
        print(p, len(law), repaired, err, bound)
        laws.append(law)
    for p, first in enumerate(laws):
        for q, second in enumerate(laws):
            d, _ = certificate(first, second)
            assert d <= Q(3,8)*(Q(1,2**p)+Q(1,2**q))
    rng = Random(20261120)
    for _ in range(300):
        a, b, c = (random_law(rng) for _ in range(3))
        ab, _ = certificate(a, b)
        bc, _ = certificate(b, c)
        ac, _ = certificate(a, c)
        assert ac <= ab+bc
    # Noisy CDF against an endpoint atom, many zero weights, identical laws.
    for x in (Q(0), Q(1), Q(1,2)):
        atom = [(x, Q(1))]
        assert certificate(atom, atom) == (0, 1)
    print("49 cross-level checks and 300 exact transport triples passed.")


if __name__ == "__main__":
    main()
