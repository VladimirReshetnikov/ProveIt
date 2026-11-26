"""Rigorous rational lower bounds for the three level-71 Hecke theta series."""
from fractions import Fraction as Q
from math import factorial, isqrt

FORMS = ((1, 1, 18), (2, 1, 9), (4, 3, 5), (3, 1, 6))
N = 24


def times(I, J):
    products = [x*y for x in I for y in J]
    return min(products), max(products)


def plus(I, J):
    return I[0]+J[0], I[1]+J[1]


def representation_counts(form):
    a, b, c = form
    assert 4*a*c - b*b == 71
    counts = [0] * (N+1)
    for y in range(-isqrt(4*a*N//71), isqrt(4*a*N//71)+1):
        radius = isqrt(4*a*N-71*y*y)
        for x in range(-((radius+b*y)//(2*a)), (radius-b*y)//(2*a)+1):
            counts[a*x*x+b*x*y+c*y*y] += 1
    return counts


def minimal_polynomial(t):
    return t**3 + t*t - 2*t - 1


def verify(root, rows):
    # Fourier coefficient = (r0+t*r1+(t^2-2)*r2+(1-t-t^2)*r3)/2.
    coefficients = []
    for r0, r1, r2, r3 in rows[1:]:
        c0 = Q(r0-2*r2+r3, 2)
        c1 = Q(r1-r3, 2)
        c2 = Q(r2-r3, 2)
        coefficients.append(plus((c0,c0), times(root, plus((c1,c1), times(root, (c2,c2))))))
    r = Q(12,25)
    tail = r**N * ((N+1)/(1-r)+r/(1-r)**2)
    lower = []
    for i in range(24):
        box = Q(i,50), Q(i+1,50)
        value = Q(0), Q(0)
        for c in reversed(coefficients):
            value = plus(c, times(box, value))
        lower.append(value[0]-tail)
    return min(lower)


if __name__ == "__main__":
    # pi>3.14 and sqrt(71)<8.45 imply 2pi/sqrt(71)>37/50.
    assert Q(628,100)/Q(845,100) > Q(37,50) and Q(845,100)**2 > 71
    assert sum(Q(37,50)**k/factorial(k) for k in range(5)) > Q(25,12)
    rows = list(zip(*(representation_counts(f) for f in FORMS)))
    for lo in (12469, -4451, -18020):
        I = Q(lo, 10000), Q(lo+1, 10000)
        assert minimal_polynomial(I[0])*minimal_polynomial(I[1]) < 0
        bound = verify(I, rows)
        k = int(1000*bound)
        assert k > 0
        print(f"root enclosed at [{float(I[0]):.4f},{float(I[1]):.4f}]: f(q)/q >= {k}/1000")
