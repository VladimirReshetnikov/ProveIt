#!/usr/bin/env python3
"""Verify the global maximum defining the rank-two Gram constant.

All comparisons use integers or Fraction. Run with Python 3.9+.
"""
from fractions import Fraction as Q
from math import isqrt, prod
from itertools import product as sign_choices
import json


def totients(n):
    phi = list(range(n + 1))
    for p in range(2, n + 1):
        if phi[p] == p:
            for k in range(p, n + 1, p):
                phi[k] -= phi[k] // p
    return phi


P = totients(20000)
S = 10**16


def ceil_ratio(n, d):
    return -((-n) // d)


def sqrt_bracket(n):
    a = isqrt(n * S * S)
    return a, a + 1


def f_bracket(t):
    """Bounds on F(t) via rational bounds on every square root."""
    a, b = t.numerator, t.denominator
    lo, hi = Q(0), Q(0)
    for j in range(1, a // b + 1):
        z = a*a - (j*b)**2
        v, w = sqrt_bracket(z)
        c = Q(P[j] * z, j)
        lo += c * v
        hi += c * w
    unit = Q(4*b, 3*a**4*S)
    return unit*lo, unit*hi


def derivative_sign(t):
    """Certified sign of sum_j (phi(j)/j)(4j²-t²)sqrt(t²-j²)."""
    a, b = t.numerator, t.denominator
    lo, hi = Q(0), Q(0)
    for j in range(1, a // b + 1):
        v, w = sqrt_bracket(a*a - (j*b)**2)
        c = Q(P[j] * (4*(j*b)**2 - a*a), j)
        lo += min(c*v, c*w)
        hi += max(c*v, c*w)
    if lo > 0:
        return 1
    if hi < 0:
        return -1
    raise ArithmeticError("Derivative sign needs greater precision")


def tail_bound():
    # For T >= 20000 the function (log(T)+3)/T decreases.
    # e > 65/24 by its power series. Hence log(20000)<10.
    assert Q(65, 24)**10 > 20000
    # Classical Archimedean rational bounds 223/71 < pi < 22/7.
    bound = 3/(2*Q(223, 71)) + Q(4*13, 3*20000)
    assert bound < Q(4787, 10000)
    return bound


def middle_bound():
    # Check A(x) = sum_{1<=j<=x} phi(j)/j <= .608 x + .6
    # with a common upper rounding denominator.
    q = 10**9
    a = 0
    for j in range(1, 20001):
        a += ceil_ratio(P[j]*q, j)
        assert 125*a <= (76*j + 75)*q
    # Partial summation, integral of (1-x^2)^{3/2} = 3 pi/16.
    bound = Q(76, 125)*Q(22, 7)/4 + Q(4, 3)*Q(3, 5)/1000
    assert bound < Q(4787, 10000)
    return bound


def low_bound():
    # Scale both endpoints by M. On [a/M,b/M], bound 1/T by M/a
    # and each increasing term (1-(j/T)^2)^{3/2} by its right endpoint.
    m, den = 10**5, 10**9
    upper_weights = [0] + [ceil_ratio(P[j]*den, j) for j in range(1, 1001)]
    leaves = 0
    stack = [(m, 615*m//100), (660*m//100, 1000*m)]
    while stack:
        a, b = stack.pop()
        total = 0
        for j in range(1, b//m + 1):
            z = b*b - (j*m)**2
            total += upper_weights[j] * z * (isqrt(z) + 1)
        # 4 M total/(3 a b^3 den) < 4787/10000
        if 40000*m*total < 4787*3*a*b**3*den:
            leaves += 1
        else:
            mid = (a+b)//2
            assert a < mid < b, (a,b)
            stack.extend([(a, mid), (mid, b)])
    return leaves


def decimal_interval(lo, hi, places=12):
    def fmt(integer):
        return f"{integer//10**places}.{integer%10**places:0{places}d}"
    scale = 10**places
    return [fmt(lo.numerator*scale//lo.denominator),
            fmt(ceil_ratio(hi.numerator*scale, hi.denominator))]


# Degree certificate for the algebraic constant u = T_star^2.
# At each x in F_53, take the product over signs of radicals 2,...,6
# in the algebra with basis sqrt(prod_{j in subset}(x-j^2)).
def norm_value(x, p):
    square = [1]
    for j in range(1, 7):
        square += [v*(x-j*j) % p for v in square]
    # Besides the norm, carry its two formal directional derivatives.
    # A_j changes by s * [j=1] sqrt(x-1) or
    # by t * (30 phi(j)/j)(x-j^2) sqrt(x-j^2).
    a = {}
    for j in range(1, 7):
        w = 30*P[j]//j
        a[1 << (j-1)] = (w*(4*j*j-x) % p, int(j == 1), w*(x-j*j) % p)
    for bit in (2,4,8,16,32):
        new = {}
        for k, (c, cs, ct) in a.items():
            for l, (d, ds, dt) in a.items():
                if bool(k & bit) == bool(l & bit):
                    factor = (-1 if k & bit else 1)*square[k & l]
                    h = k ^ l
                    u,v,w = new.get(h,(0,0,0))
                    new[h] = ((u+factor*c*d) % p,
                              (v+factor*(c*ds+d*cs)) % p,
                              (w+factor*(c*dt+d*ct)) % p)
        a = {k:c for k,c in new.items() if any(c)}
    assert set(a) <= {0}
    return a.get(0,(0,0,0))


def trimmed(poly):
    while poly and poly[-1] == 0:
        poly.pop()
    return poly


def remainder(a, b, p):
    v = a[:]
    inv = pow(b[-1],-1,p)
    while len(v) >= len(b):
        lead, offset = v[-1]*inv % p, len(v)-len(b)
        for j,c in enumerate(b):
            v[offset+j] = (v[offset+j]-lead*c) % p
        trimmed(v)
    return v


def product(a, b, p):
    v = [0]*(len(a)+len(b)-1)
    for i,f in enumerate(a):
        for j,g in enumerate(b):
            v[i+j] = (v[i+j]+f*g) % p
    return trimmed(v)


def poly_power(a, k, modulus, p):
    out = [1]
    while k:
        if k & 1:
            out = remainder(product(out,a,p),modulus,p)
        a = remainder(product(a,a,p),modulus,p)
        k //= 2
    return out


def interpolate(values, p):
    diff, coefficients, basis = list(values), [0]*49, [1]
    for i in range(49):
        for k,b in enumerate(basis):
            coefficients[k] = (coefficients[k]+diff[0]*b) % p
        diff = [(v-u)%p for u,v in zip(diff,diff[1:])]
        basis = [b*pow(i+1,-1,p)%p for b in product(basis,[-i,1],p)]
    return trimmed(coefficients)


def algebraic_degree():
    # The norm and its two directional derivatives have degree at most 48.
    p = 53
    values = [norm_value(j,p) for j in range(49)]
    coefficients, hs, ht = [interpolate(v,p) for v in zip(*values)]
    assert coefficients[48] != 0
    # Rabin irreducibility in F_p[X]: n=48 has prime divisors 2,3.
    xpower = [0,1]
    for d in range(1,49):
        xpower = poly_power(xpower,p,coefficients,p)
        if d in (16,24):
            diff = xpower+[0]*max(0,2-len(xpower))
            diff[1] = (diff[1]-1)%p
            a,b = coefficients,trimmed(diff)
            while b:
                a,b = b,remainder(a,b,p)
            assert len(a)==1
    assert xpower == [0,1]
    # kappa = 2025 u^4 H_s(u)^2 / [256 (u-1) H_t(u)^2].
    # A nonzero scalar in F_p leaves the orbit size invariant.
    num = remainder(product([0,0,0,0,1], product(hs,hs,p),p),coefficients,p)
    den = remainder(product([p-1,1], product(ht,ht,p),p),coefficients,p)
    assert num and den
    n,d = num,den
    for i in range(1,25):
        n = poly_power(n,p,coefficients,p)
        d = poly_power(d,p,coefficients,p)
        if i in (16,24):
            assert (remainder(product(n,den,p),coefficients,p) !=
                    remainder(product(d,num,p),coefficients,p))
    weights = (30,15,20,15,24,10)
    leading = prod(sum(a*b for a,b in zip((1,*e),weights))
                   for e in sign_choices((-1,1),repeat=5))
    assert leading%53 == coefficients[-1]
    for x,q,v in [(0,53,50),(1,59,42)]:
        norm = norm_value(x,q)[0]*pow(leading,-1,q) % q
        assert norm == v and pow(norm,(q-1)//2,q) == q-1
    return {"degree_of_T_star_squared":48, "degree_of_kappa":48,
            "degree_of_T_star":96, "degree_of_C":96,
            "irreducible_modulo":p,
            "coefficients_mod_53_ascending":coefficients}


def main():
    leaves = low_bound()
    mid_bound, far_bound = middle_bound(), tail_bound()
    lo, hi = Q(615, 100), Q(660, 100)
    assert f_bracket(Q(635,100))[0] > Q(47879,100000)
    assert (derivative_sign(lo), derivative_sign(hi)) == (1, -1)
    for _ in range(51):
        mid = (lo+hi)/2
        if derivative_sign(mid) > 0:
            lo = mid
        else:
            hi = mid
    lower = f_bracket((lo+hi)/2)[0]
    # Ratio bound by monotonicity of T F(T) throughout the interval.
    upper = f_bracket(hi)[1]*hi/lo
    result = {
        "global_exclusion_threshold": "0.4787",
        "finite_interval_count": leaves,
        "algebraic_degree_certificate": algebraic_degree(),
        "middle_upper_bound": str(mid_bound),
        "tail_upper_bound": str(far_bound),
        "F_at_6.35_lower_bound": "0.47879",
        "T_star_interval": decimal_interval(lo, hi),
        "C_interval": decimal_interval(lower, upper),
        "kappa_interval": decimal_interval(1/(64*upper**2), 1/(64*lower**2))
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
