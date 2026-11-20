"""Bounded algorithms for approximate IVT and polynomial crossing. Python 3.10+."""
from fractions import Fraction as F
from math import factorial, isqrt


def eps(k):
    return F(1, 2**k)


def ceil_log2(v):
    assert v >= 1
    return (v - 1).bit_length()


def approx_zero(eval_at, modulus, k):
    """Supply a weak initial bracket on [0,1]; return point and number of calls."""
    a, b = F(0), F(1)
    p = k + 2
    count = 0
    for _ in range(modulus(k + 1)):
        x = (a + b) / 2
        v = eval_at(x, p)
        count += 1
        if abs(v) <= eps(p):
            return x, count
        if v > 0:
            b = x
        else:
            a = x
    return (a + b) / 2, count


def horner(coeffs, x):
    result = F(0)
    for c in reversed(coeffs):
        result = result * x + c
    return result


def root_steps(d, coefficient, stages):
    """Yield the canonical bracket and its verifiable node certificate each stage."""
    assert d >= 1
    a, b = F(0), F(1)
    for n in range(stages):
        p = d * (ceil_log2(6 * d) + 2 * n) + 3
        s = p + ceil_log2(d)
        table = [coefficient(i, s) for i in range(d)] + [F(1)]
        w = b - a
        h = w / (3 * d)
        nodes = [a + w / 3 + i * h for i in range(d + 1)]
        values = [horner(table, z) for z in nodes]
        index = max(range(d + 1), key=lambda i: abs(values[i]))
        z, v = nodes[index], values[index]
        certificate = (n, a, b, z, v, h, p, s, values)
        if v > 0:
            b = z
        else:
            a = z
        yield (a, b), certificate


def run_checks():
    checks = {"finite_difference": 0, "bracket": 0, "modulus": 0, "approx_ivt": 0}

    def inspect(d, coefficient, left_sign, right_sign, stages=32):
        sample_calls = []
        def counted(i, s):
            sample_calls.append((i, s))
            return coefficient(i, s)
        mids = [F(1, 2)]
        for (a, b), cert in root_steps(d, counted, stages):
            n, old_a, old_b, z, v, h, p, s, row = cert
            while len(row) > 1:
                row = [y - x for x, y in zip(row, row[1:])]
            assert row[0] == factorial(d) * h**d
            assert row[0] <= 2**d * abs(v)
            assert abs(v) >= 8 * eps(p)
            assert d * eps(s) <= eps(p)
            checks["finite_difference"] += 1
            assert old_a <= a < b <= old_b
            assert 3*(b-a) <= 2*(old_b-old_a)
            assert 3*(b-a) >= old_b-old_a
            assert left_sign(a) and right_sign(b)
            checks["bracket"] += 1
            if n % 2 == 1:
                mids.append((a+b)/2)
                assert b-a <= eps(len(mids)-1)
        assert len(sample_calls) == d * stages
        for k, x in enumerate(mids):
            for y in mids[k:]:
                assert abs(x - y) <= eps(k+1)
                checks["modulus"] += 1
        return mids

    # Two names of the same monic cubic deliberately lead to different roots.
    cubic = [F(-3, 32), F(11, 16), F(-3, 2), F(1)]
    for displacement, selected_root in [(1, F(1, 4)), (-1, F(3, 4))]:
        def cubic_name(i, s):
            return cubic[i] + (displacement * eps(s) if i == 0 else 0)
        output = inspect(3, cubic_name,
            lambda z: horner(cubic, z) <= 0, lambda z: horner(cubic, z) >= 0)
        for k, x in enumerate(output):
            assert abs(x - selected_root) <= eps(k+1)

    # A double root and an irrational coefficient. Independent bracket checks
    # use 16*x^6 compared with 2, an exact sign comparison for x^3-sqrt(2)/4.
    # P=(x-1/2)^2 (x^3 - sqrt(2)/4).
    def quadratic_irrational_name(i, s):
        alpha = F(isqrt(2 * 2**(2*s)), 4 * 2**s)
        return [-alpha / 4, alpha, -alpha, F(1,4), F(-1)][i]
    inspect(5, quadratic_irrational_name,
        lambda z: 16 * z**6 <= 2,
        lambda z: 16 * z**6 >= 2)

    # An odd repeated root with zero derivative at its only crossing.
    flat = [F(-1,8), F(3,4), F(-3,2), F(1)]
    inspect(3, lambda i,s: flat[i] + (eps(s)/2 if i == 2 else 0),
        lambda z: z <= F(1,2), lambda z: z >= F(1,2))

    g = lambda x: min(x - F(1,3), F(0)) + max(x - F(2,3), F(0))
    for shift in [F(0), F(1,2**10), F(-1,2**10)]:
        for k in range(24):
            f = lambda x: g(x) + shift
            # An admissible evaluator that systematically rounds upward.
            z, calls = approx_zero(lambda x,p: f(x) + eps(p), lambda j: j, k)
            assert abs(f(z)) <= eps(k+1) and calls <= k+1
            checks["approx_ivt"] += 1
    return checks


if __name__ == "__main__":
    import json
    print(json.dumps(run_checks(), sort_keys=True))
