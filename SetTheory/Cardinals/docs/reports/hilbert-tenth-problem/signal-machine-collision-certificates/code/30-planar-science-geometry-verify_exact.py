"""Fresh exact algebra checks supporting, not proving, PROOF.md.

No external files or programs are loaded. No signal trajectories are simulated.
Only Python standard-library rational arithmetic is used.
"""

from fractions import Fraction as F
import json
from math import gcd, lcm


def mat(rows):
    return tuple(tuple(F(x) for x in row) for row in rows)


I = mat(((1, 0), (0, 1)))
Z = mat(((0, 0), (0, 0)))


def add(a, b):
    return tuple(tuple(a[i][j] + b[i][j] for j in range(2)) for i in range(2))


def scale(s, a):
    return tuple(tuple(s * x for x in row) for row in a)


def mul(a, b):
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(2))
                       for j in range(2)) for i in range(2))


def tr(a):
    return tuple(tuple(a[j][i] for j in range(2)) for i in range(2))


def inv(a):
    d = a[0][0]*a[1][1] - a[0][1]*a[1][0]
    assert d
    return scale(1/d, ((a[1][1], -a[0][1]), (-a[1][0], a[0][0])))


def powmat(a, n):
    out = I
    for _ in range(n):
        out = mul(out, a)
    return out


def mv(a, x):
    return tuple(sum(a[i][j]*x[j] for j in range(2)) for i in range(2))


def dot(x, y):
    return sum(a*b for a, b in zip(x, y))


def quadratic(q, x):
    return dot(x, mv(q, x))


def ellipse_checks():
    count = 0
    for t in (F(-7, 4), F(-1), F(-1, 2), F(0), F(1, 2), F(1), F(7, 4)):
        c = mat(((0, -1), (1, t)))
        h = mat(((1, t/2), (t/2, 1)))
        assert mul(mul(tr(c), h), c) == h
        assert 1-t*t/4 > 0
        for s in (I, mat(((2, 1), (-1, 3))), mat(((1, -2), (3, 1)))):
            a = mul(mul(s, c), inv(s))
            q = mul(mul(tr(inv(s)), h), inv(s))
            assert mul(mul(tr(a), q), a) == q
            for row, b in (((F(1), F(0)), F(1)),
                           ((F(0), F(-1)), F(2)),
                           ((F(2), F(3)), F(5))):
                qih = mv(inv(q), row)
                d = dot(row, qih)
                p = tuple(b*z/d for z in qih)
                assert dot(row, p) == b
                assert quadratic(q, p) == b*b/d
                count += 1
    return count


def mixed_checks():
    count = 0
    s = mat(((2, 1), (-1, 3)))
    for eps in (F(-1), F(1)):
        for mu in (F(-3, 4), F(-1, 2), F(0), F(1, 3), F(3, 4)):
            d = mat(((eps, 0), (0, mu)))
            a = mul(mul(s, d), inv(s))
            e = scale(1/(eps-mu), add(a, scale(-mu, I)))
            f = add(I, scale(-1, e))
            assert mul(e, e) == e
            assert mul(f, f) == f
            assert mul(e, f) == Z
            assert a == add(scale(eps, e), scale(mu, f))
            for k in range(8):
                for j in range(2):
                    expected = add(scale(eps**j, e), scale((mu*mu)**k * mu**j, f))
                    assert powmat(a, 2*k+j) == expected
                    count += 1
    return count


def facet_checks():
    records = []
    for m in (4, 5, 8, 16, 32, 64):
        lam = F(m-1, m)
        delta = 1-lam
        a = mat(((lam, 1), (0, lam)))
        nmax = (m-1)//2
        def xn(n):
            return lam**(-n) * (1-n*delta/lam)
        def fn(n, x):
            return lam**(1-n)/n-lam*x/n
        for n in range(1, nmax+1):
            assert xn(n)-xn(n-1) == -n*delta*delta*lam**(-n-1)
            assert fn(n, xn(n)) == delta*lam**(-n)
            assert fn(n+1, xn(n)) == fn(n, xn(n))
            x = (xn(n)+xn(n-1))/2
            y = fn(n, x)
            assert 0 < x < 1 and 0 < y < 1
            assert lam**n*x+n*lam**(n-1)*y == 1
            # The universal all-j assertion is proved by adjacent comparisons.
            # This bounded range checks finite fixtures only.
            for j in range(1, 4*m+1):
                if j != n:
                    assert y < fn(j, x)
            for j in range(1, min(20, 4*m)+1):
                expected = mat(((lam**j, j*lam**(j-1)), (0, lam**j)))
                assert powmat(a, j) == expected
        records.append({"M": m, "checked_active_facet_lines": nmax})
    return records


def degeneracy_checks():
    for a in (mat(((0, 1), (0, 0))), Z):
        assert powmat(a, 2) == Z
    for eps in (-1, 1):
        a = mat(((eps, 1), (0, eps)))
        for n in range(1, 12):
            assert powmat(a, n) == mat(((eps**n, n*eps**(n-1)), (0, eps**n)))
    # Limit equality can be valid for nonzero contraction.
    x, y = F(1), F(-1, 2)
    for n in range(100):
        assert x+F(1, 2)**n*y < 1
    # For stable eigenvalue zero and epsilon=-1, time2 is indispensable.
    # P={-2<x<3/2, -1<y<1, x+y<1} contains0.
    a = mat(((-1, 0), (0, 0)))
    z = (F(1), F(-1, 2))
    def p(v):
        return -2 < v[0] < F(3, 2) and -1 < v[1] < 1 and v[0]+v[1] < 1
    assert p(z) and p(mv(a, z))
    assert not p(mv(powmat(a, 2), z))
    return True


def denominator_checks():
    count = 0
    for aa, q in ((1, 2), (-1, 2), (3, 2), (-3, 2), (5, 6), (-5, 6), (13, 15)):
        assert gcd(aa, q) == 1 and abs(aa) < 2*q and q >= 2
        c = mat(((0, -1), (1, F(aa, q))))
        for n in range(1, 41):
            v = mv(powmat(c, n), (F(1), F(0)))
            assert lcm(v[0].denominator, v[1].denominator) == q**(n-1)
            count += 1
    return count


if __name__ == "__main__":
    result = {
        "status": "passed",
        "ellipse_contact_identity_checks": ellipse_checks(),
        "mixed_projector_power_checks": mixed_checks(),
        "facet_fixtures": facet_checks(),
        "degeneracy_checks": degeneracy_checks(),
        "companion_denominator_checks": denominator_checks(),
        "scope": "Finite exact algebra fixtures only; conventional proof is separate.",
    }
    print(json.dumps(result, indent=2))
