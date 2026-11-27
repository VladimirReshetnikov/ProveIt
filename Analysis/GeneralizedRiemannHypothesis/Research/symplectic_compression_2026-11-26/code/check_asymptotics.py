"""Exact polynomial/rational checks of the first correction and two-plane law."""

from fractions import Fraction
from itertools import product
from pathlib import Path
import json

from audit_symplectic_counts import Field, embeddings, expected_count, transverse_count


def add(p, q):
    out = [0] * max(len(p), len(q))
    for i, c in enumerate(p):
        out[i] += c
    for i, c in enumerate(q):
        out[i] += c
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def mul(p, q):
    out = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def value(p, z):
    out = Fraction(0)
    for coeff in reversed(p):
        out = out * z + coeff
    return out


def C(q, u):
    out = [1]
    for j in range(u):
        out = mul(out, [1, -(q ** (2 * j))])
    return out


def A(q, u):
    return sum(q ** (2 * j) for j in range(u))


def invariants(f, h1, h0, m):
    a, b = len(h1), len(h0)
    gamma = [list(h1[i]) + list(m[i]) for i in range(a)]
    gamma += [[f.neg(m[i][j]) for i in range(a)] + list(h0[j]) for j in range(b)]
    s = f.rank(gamma) // 2
    r = a + b - 2 * s
    t0 = b - f.rank(list(h0) + list(m))
    t1 = a - f.rank(list(h1) + [tuple(m[i][j] for i in range(a)) for j in range(b)])
    return s, r, t0, t1


def likelihood_polynomials(f, h1, h0, m):
    a, b = len(h1), len(h0)
    d = a + b
    s1, s0 = f.rank(h1) // 2, f.rank(h0) // 2
    s, r, t0, t1 = invariants(f, h1, h0, m)
    numerator = [0]
    for ell in range(r + 1):
        t = transverse_count(f.q, r, t0, t1, ell)
        scalar = t * f.q ** (d * ell - ell * (ell + 1) // 2)
        numerator = add(numerator, [0] * ell + [scalar * c for c in C(f.q, d - ell - s)])
    denominator = mul(C(f.q, a - s1), C(f.q, b - s0))
    t1_closed = (f.q ** r - f.q ** t0 - f.q ** t1 + 1) // (f.q - 1)
    k = f.q ** (d - 1) * t1_closed - A(f.q, d - s) + A(f.q, a - s1) + A(f.q, b - s0)
    assert numerator[0] == denominator[0] == 1
    derivative = (numerator[1] if len(numerator) > 1 else 0) - (denominator[1] if len(denominator) > 1 else 0)
    assert derivative == k
    return numerator, denominator, k


def det2(f, m):
    return f.add(f.mul(m[0][0], m[1][1]), f.neg(f.mul(m[0][1], m[1][0])))


def verify(q):
    f = Field(q)
    j = ((0, 1), (f.neg(1), 0))
    zero = ((0, 0), (0, 0))
    cases = []
    for h1_name, h1 in [("zero", zero), ("symplectic", j)]:
        for h0_name, h0 in [("zero", zero), ("symplectic", j)]:
            ks = []
            marginal = [0] * q
            plane_distributions = {n: [] for n in (1, 2, 3)}
            for flat in product(range(q), repeat=4):
                m = (flat[:2], flat[2:])
                num, den, k = likelihood_polynomials(f, h1, h0, m)
                ks.append(k)
                marginal[m[0][0]] += k
                # At n=2 all prescribed 2-dimensional forms are realizable.
                z = Fraction(1, q ** 4)
                exact_density = Fraction(q ** 4 * expected_count(f, 2, h1, h0, m),
                                         embeddings(q, 2, 2, f.rank(h0) // 2))
                assert value(num, z) / value(den, z) == exact_density
                if h1 == h0 == j:
                    critical = det2(f, m) == 1
                    simple_num = [1, q ** 3 - q ** 2] if critical else [1, -(q ** 2)]
                    # Exact polynomial identity, not numerical approximation.
                    assert mul(num, [1, -1]) == mul(den, simple_num)
                    for n in plane_distributions:
                        zn = Fraction(1, q ** (2 * n))
                        density = value(simple_num, zn) / (1 - zn)
                        plane_distributions[n].append(density / q ** 4)
            assert sum(ks) == 0
            assert marginal == [q ** 3 * (1 - q)] + [q ** 3] * (q - 1)
            case = {"q": q, "H1": h1_name, "H0": h0_name,
                    "matrices_checked": q ** 4,
                    "K_min": min(ks), "K_max": max(ks), "K_sum": sum(ks),
                    "leading_TV_coefficient": str(Fraction(sum(abs(k) for k in ks), 2 * q ** 4)),
                    "scalar_K_marginal": marginal,
                    "first_derivative_identity": True,
                    "exact_density_at_n2": True}
            if h1 == h0 == j:
                tvs = {}
                for n, probabilities in plane_distributions.items():
                    assert sum(probabilities) == 1
                    tv = sum(abs(p - Fraction(1, q ** 4)) for p in probabilities) / 2
                    claimed = Fraction((q ** 3 - q ** 2 + 1) * (q ** 2 - 1),
                                       q ** 3 * (q ** (2 * n) - 1))
                    assert tv == claimed
                    tvs[str(n)] = str(tv)
                case.update(two_plane_symbolic_identity=True, exact_two_plane_TV=tvs)
            cases.append(case)
    return cases


def main():
    cases = verify(2) + verify(3)
    result = {"arithmetic": "integer polynomials and fractions.Fraction only",
              "all_passed": True,
              "total_matrix_cases": sum(c["matrices_checked"] for c in cases),
              "cases": cases}
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
