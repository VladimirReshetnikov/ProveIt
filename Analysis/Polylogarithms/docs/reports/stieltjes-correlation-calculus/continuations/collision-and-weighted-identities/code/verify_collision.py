"""Independent subtracted real-integral checks of colliding polygammas.

No meromorphic spectral kernel is used on the numerical left hand side.
The right hand side is the all-order closed formula derived in collision.tex.
"""
from fractions import Fraction
from math import gcd, factorial
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 44


def pg(r, x):
    return mp.digamma(x) if r == 0 else mp.polygamma(r, x)


def regular_tail(r, a, scale, order, t):
    """(f(a+scale*t)-Taylor_order(f))/t**(order+1), stably."""
    y = scale * t
    if abs(y) < a / 3:
        # Expansion is geometric apart from polynomial coefficient growth.
        total = mp.mpf(0)
        power = mp.mpf(scale) ** (order + 1)
        for j in range(order + 1, order + 1 + 500):
            term = pg(r+j, a) * power / mp.factorial(j)
            total += term
            if j > order + 3 and abs(term) < mp.eps * max(1, abs(total)):
                return total
            power *= y
        raise RuntimeError("Taylor remainder failed to converge")
    value = pg(r, a + y)
    for j in range(order + 1):
        value -= pg(r+j, a) * y**j / mp.factorial(j)
    return value / t**(order+1)


def primitive_power(exponent, ell):
    return mp.log(ell) if exponent == -1 else ell**(exponent+1)/(exponent+1)


def fp_integral(p, q, r, k):
    points = sorted({Fraction(j,p) for j in range(p+1)} |
                    {Fraction(j,q) for j in range(q+1)})
    value = mp.mpf(0)
    for left, right in zip(points, points[1:]):
        ell = mp.mpf((right-left).numerator) / (right-left).denominator
        ap = (p*left) % 1
        aq = (q*left) % 1
        sing_p, sing_q = ap == 0, aq == 0
        ap = mp.mpf(1) if sing_p else mp.mpf(ap.numerator)/ap.denominator
        aq = mp.mpf(1) if sing_q else mp.mpf(aq.numerator)/aq.denominator
        cp = (-1)**(r+1)*mp.factorial(r)/mp.mpf(p)**(r+1)
        cq = (-1)**(k+1)*mp.factorial(k)/mp.mpf(q)**(k+1)
        if sing_p and sing_q:
            value += cp*cq*primitive_power(-r-k-2, ell)
        if sing_p:
            for j in range(r+1):
                c = cp*pg(k+j,aq)*mp.mpf(q)**j/mp.factorial(j)
                value += c*primitive_power(j-r-1,ell)
        if sing_q:
            for j in range(k+1):
                c = cq*pg(r+j,ap)*mp.mpf(p)**j/mp.factorial(j)
                value += c*primitive_power(j-k-1,ell)

        def regularized(t):
            result = pg(r,ap+p*t)*pg(k,aq+q*t)
            if sing_p:
                result += cp*regular_tail(k,aq,q,r,t)
            if sing_q:
                result += cq*regular_tail(r,ap,p,k,t)
            return result

        value += mp.quad(regularized,[0,ell/2,ell])
    return value


def closed(p,q,r,k):
    d=gcd(p,q)
    P,Q=p//d,q//d
    K=mp.log(p*q//d)
    N=r+k
    if N==0:
        return (2*mp.stieltjes(1)-2*mp.zeta(2)-2*mp.euler*K-K*K+
                mp.log(p)*mp.log(q))
    h=lambda j: mp.harmonic(j) if j else mp.mpf(0)
    z, dz=mp.zeta(N+1),mp.diff(mp.zeta,N+1)
    return (mp.factorial(N)*mp.mpf(P)**k*mp.mpf(Q)**r*
            ((-1)**(k+1)*(dz+(h(N)-h(r)+K)*z)+
             (-1)**(r+1)*(dz+(h(N)-h(k)+K)*z)))


if __name__ == '__main__':
    cases=[(1,1,0,0),(2,3,0,0),(4,6,0,0),
           (2,3,0,1),(4,6,0,1),(2,3,1,0),
           (2,3,1,1),(2,3,2,1),(3,2,0,3)]
    records=[]
    for case in cases:
        lhs=fp_integral(*case)
        rhs=closed(*case)
        relative=abs(lhs-rhs)/max(1,abs(rhs))
        record={'p':case[0],'q':case[1],'r':case[2],'k':case[3],
                'subtracted_integral':mp.nstr(lhs,42),'formula':mp.nstr(rhs,42),
                'relative_residual':mp.nstr(relative,6)}
        records.append(record)
        print(json.dumps(record),flush=True)
        assert relative < mp.mpf('1e-35')
    (Path(__file__).resolve().parent.parent / 'results' / 'collision_validation.json').write_text(
        json.dumps({'precision_dps':mp.mp.dps,'checks':records,
                    'status':'floating-point consistency, not certified intervals'},indent=2))
