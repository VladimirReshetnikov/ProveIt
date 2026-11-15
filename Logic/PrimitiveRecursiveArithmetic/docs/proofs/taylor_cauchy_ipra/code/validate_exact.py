#!/usr/bin/env python3
"""Deterministic exact-arithmetic illustrations; not an iPRA/Lean proof."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from decimal import Decimal, localcontext
from fractions import Fraction as Q
import json
from math import factorial
from pathlib import Path
import sys


@dataclass(frozen=True)
class CQ:
    re: Q = Q(0)
    im: Q = Q(0)

    def __post_init__(self):
        object.__setattr__(self, "re", Q(self.re))
        object.__setattr__(self, "im", Q(self.im))

    @staticmethod
    def coerce(other):
        return other if isinstance(other, CQ) else CQ(Q(other))

    def __add__(self, other):
        z = CQ.coerce(other)
        return CQ(self.re + z.re, self.im + z.im)

    __radd__ = __add__

    def __neg__(self):
        return CQ(-self.re, -self.im)

    def __sub__(self, other):
        return self + (-CQ.coerce(other))

    def __rsub__(self, other):
        return CQ.coerce(other) - self

    def __mul__(self, other):
        z = CQ.coerce(other)
        return CQ(self.re*z.re - self.im*z.im,
                  self.re*z.im + self.im*z.re)

    __rmul__ = __mul__

    def abs2(self):
        return self.re*self.re + self.im*self.im

    def norm1(self):
        return abs(self.re) + abs(self.im)

    def inverse(self):
        den = self.abs2()
        if den == 0:
            raise ZeroDivisionError("zero rational complex denominator")
        return CQ(self.re/den, -self.im/den)

    def __truediv__(self, other):
        return self * CQ.coerce(other).inverse()

    def __rtruediv__(self, other):
        return CQ.coerce(other) / self

    def __pow__(self, n):
        if n < 0:
            return self.inverse() ** (-n)
        ans = CQ(1)
        for _ in range(n):
            ans = ans * self
        return ans


I = CQ(0, 1)
ZERO = CQ()


def rational_json(q):
    q = Q(q)
    with localcontext() as ctx:
        ctx.prec = 30
        approx = str(Decimal(q.numerator) / Decimal(q.denominator))
    return {"numerator": str(q.numerator), "denominator": str(q.denominator),
            "decimal_display_only": approx}


def complex_json(z):
    return {"real": rational_json(z.re), "imaginary": rational_json(z.im)}


def trim(p):
    p = list(map(Q, p))
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p or [Q(0)]


def poly_add(p, q):
    return trim([(p[i] if i < len(p) else 0) +
                 (q[i] if i < len(q) else 0)
                 for i in range(max(len(p), len(q)))])


def poly_mul(p, q):
    ans = [Q(0)] * (len(p) + len(q) - 1)
    for j, x in enumerate(p):
        for k, y in enumerate(q):
            ans[j+k] += x*y
    return trim(ans)


def poly_scale(p, c):
    return trim([Q(c)*x for x in p])


def poly_eval(p, x):
    ans = Q(0)
    for c in reversed(p):
        ans = ans*x + c
    return ans


def poly_derivative(p):
    return trim([j*p[j] for j in range(1, len(p))])


def poly_affine(p, a, h):
    ans = [Q(0)]
    for c in reversed(p):
        ans = poly_add(poly_mul(ans, [a, h]), [c])
    return ans


def poly_pow(p, n):
    ans = [Q(1)]
    for _ in range(n):
        ans = poly_mul(ans, p)
    return ans


def integral_01(p):
    return sum((c/Q(j+1) for j, c in enumerate(p)), Q(0))


def normalized_jet(p, a, b, count):
    h, cur, result = b-a, p, []
    for j in range(count):
        result.append(poly_scale(poly_affine(cur, a, h), h**j))
        cur = poly_derivative(cur)
    return result


def w(j, t):
    return (1-t)**j / factorial(j)


def wd(j, t):
    return Q(0) if j == 0 else -w(j-1, t)


def finite_identity_tests():
    count = 0
    for n in range(13):
        u = [Q(3*k*k-2*k+7, k+1) for k in range(n+1)]
        v = [Q(k*k*k+2, k+2) for k in range(n+1)]
        assert sum((u[k+1]-u[k] for k in range(n)), Q(0)) == u[n]-u[0]
        lhs = sum((u[k]*(v[k+1]-v[k]) for k in range(n)), Q(0))
        rhs = u[n]*v[n]-u[0]*v[0] - sum(
            (v[k+1]*(u[k+1]-u[k]) for k in range(n)), Q(0))
        assert lhs == rhs
        count += 2
        for q in [Q(-3, 4), Q(0), Q(1, 3), Q(1), Q(5, 4)]:
            assert (1-q)*sum((q**k for k in range(n)), Q(0)) == 1-q**n
            count += 1
    for j in range(9):
        for u, v in [(Q(0), Q(1,8)), (Q(2,7), Q(5,7)),
                     (Q(3,4), Q(1,4)), (Q(1), Q(1))]:
            d = v-u
            assert abs(w(j, v)) <= 1
            assert abs(w(j, v)-w(j, u)) <= abs(d)
            assert abs(w(j, v)-w(j, u)-d*wd(j,u)) <= d*d
            e_u, e_v, e_next = Q(3,7), Q(-2,5), Q(11,13)
            lhs = w(j,v)*e_v-w(j,u)*e_u-d*(w(j,u)*e_next+wd(j,u)*e_u)
            rhs = (w(j,v)*(e_v-e_u-d*e_next) +
                   d*(w(j,v)-w(j,u))*e_next +
                   (w(j,v)-w(j,u)-d*wd(j,u))*e_u)
            assert lhs == rhs
            count += 4
    for k in range(1, 16):
        f, fp = CQ(Q(k,3),Q(1,4)), CQ(Q(2,5),Q(-k,7))
        u, h, e = CQ(Q(k,2),Q(1,3)), CQ(Q(1,11),Q(k,17)), CQ(Q(1,29),Q(-1,31))
        lhs=(f+fp*h+e)/(u+h)-f/u-(fp/u-f/(u**2))*h
        rhs=e/(u+h)-fp*(h**2)/(u*(u+h))+f*(h**2)/((u**2)*(u+h))
        assert lhs == rhs
        count += 1
    return {"assertions": count, "status": "PASS"}


def affine_triangle_tests():
    alpha, beta = CQ(Q(2,3),Q(-3,7)), CQ(Q(5,11),Q(2,9))
    def f(z):
        return alpha+beta*z
    def edge(u,v):
        return (v-u)*(f(u)+f(v))/2
    def triangle(t):
        return sum((edge(t[j],t[(j+1)%3]) for j in range(3)), ZERO)
    count = 0
    for k in range(1, 13):
        a, b, c = CQ(-k,Q(1,3)), CQ(Q(2*k,3),-1), CQ(Q(1,7),Q(k+1,2))
        ab, bc, ca = (a+b)/2, (b+c)/2, (c+a)/2
        children = [(a,ab,ca),(ab,b,bc),(ca,bc,c),(ab,bc,ca)]
        assert triangle((a,b,c)) == ZERO
        assert all(triangle(t) == ZERO for t in children)
        assert sum((triangle(t) for t in children),ZERO) == triangle((a,b,c))
        for u,v in [(a,b),(b,c),(c,a)]:
            m=(u+v)/2
            assert edge(u,v) == edge(u,m)+edge(m,v)
            assert edge(u,v) == -edge(v,u)
        count += 9
    return {"assertions": count, "status": "PASS",
            "integral_rule": "(v-u)*(f(u)+f(v))/2; exact for affine f"}


def taylor_polynomial_tests():
    cases=[]
    polynomials=[[Q(1),Q(-2),Q(3,2),Q(-1,6),Q(5,24)],
                 [Q(1),Q(1),Q(1),Q(1)],
                 [Q(2,7),Q(-3,11),Q(0),Q(5,13),Q(1,17),Q(-2,19)]]
    count=0
    for p in polynomials:
        for a,b in [(Q(0),Q(1)),(Q(2,3),Q(-1,4)),(Q(1,2),Q(1,2))]:
            for n in range(6):
                jet=normalized_jet(p,a,b,n+2)
                polynomial=sum((poly_eval(jet[j],Q(0))/factorial(j) for j in range(n+1)),Q(0))
                integrand=poly_scale(poly_mul(poly_pow([Q(1),Q(-1)],n),jet[n+1]),Q(1,factorial(n)))
                remainder=integral_01(integrand)
                lhs=poly_eval(p,b)-polynomial
                assert lhs == remainder
                beta=sum(map(abs,jet[n+1]),Q(0))
                assert abs(remainder) <= beta/factorial(n+1)
                count += 2
    # Literal common-precision certificate (F) from the paper.
    n,N,p,r=2,64,16,4
    jet=normalized_jet([Q(1),Q(1),Q(1),Q(1)],Q(0),Q(1),n+2)
    beta=[max(Q(1),sum(map(abs,q),Q(0))) for q in jet]
    delta,eps=Q(1,N),Q(1,2**p)
    def sample(j,i):
        value=poly_eval(jet[j],Q(i,N))
        return Q((value*2**p).__floor__(),2**p)
    for j in range(n+2):
        for i in range(N+1):
            assert abs(sample(j,i)-poly_eval(jet[j],Q(i,N))) <= eps
            assert abs(sample(j,i)) <= beta[j]+eps
            count += 2
    for j in range(n+1):
        for i in range(N):
            local=sample(j,i+1)-sample(j,i)-delta*sample(j+1,i)
            assert abs(local) <= delta*Q(1,2**r)+(2+delta)*eps
            count += 1
    G=[sum((w(j,Q(i,N))*sample(j,i) for j in range(n+1)),Q(0)) for i in range(N+1)]
    D=[w(n,Q(i,N))*sample(n+1,i) for i in range(N)]
    C=sum((beta[j]+beta[j+1]+2 for j in range(n+1)),Q(0))
    cell_bound=(n+1)*delta*Q(1,2**r)+(n+1)*(2+delta)*eps+delta**2*C
    for i in range(N):
        assert abs(G[i+1]-G[i]-delta*D[i]) <= cell_bound
        count += 1
    defect=sample(0,N)-sum((sample(j,0)/factorial(j) for j in range(n+1)),Q(0))-delta*sum(D,Q(0))
    bound=(n+1)*Q(1,2**r)+(n+1)*(2*N+1)*eps+C/N
    assert abs(defect) <= bound
    assert N*cell_bound == bound
    count += 2
    return {"assertions":count,"status":"PASS", "polynomial_cases":54,
            "finite_certificate":{"n":n,"N":N,"p":p,"r":r,
                "C":rational_json(C),"defect":rational_json(defect),
                "bound":rational_json(bound),"comparison":True}}


def trapezoid(values,N):
    return (sum(values[1:-1],values[0]*0)+(values[0]+values[-1])/2)/N


def circle_cauchy_certificate(N):
    """Certified quadrature comparison; see README for the derivative bounds."""
    a=CQ(Q(1,4),Q(1,8))
    def f(z):
        return 1+z+z*z
    def beta(t):
        return (1+I*t)/(1-I*t)
    def beta_prime(t):
        return 2*I/((1-I*t)**2)
    integral_approx=ZERO
    checks=0
    for quarter in range(4):
        rotation=I**quarter
        values=[]
        for k in range(N+1):
            t=Q(k,N)
            z=rotation*beta(t)
            zp=rotation*beta_prime(t)
            assert z.abs2()==1
            assert beta_prime(t)/beta(t)==2*I/(1+t*t)
            assert f(z)/(z-a)==z+(1+a)+f(a)/(z-a)
            # Finite form underlying the independent shifted-kernel argument.
            q=a/z
            m=5
            assert (1-q)*sum((q**j for j in range(m)),ZERO)==1-q**m
            assert (z-a).abs2() >= Q(5,8)**2
            checks += 5
            values.append(f(z)/(z-a)*zp)
        integral_approx += trapezoid(values,N)
    reciprocal_values=[Q(1)/(1+Q(k,N)**2) for k in range(N+1)]
    pi_mid=4*trapezoid(reciprocal_values,N)
    pi_error=Q(2,3*N*N)
    pi_lo,pi_hi=pi_mid-pi_error,pi_mid+pi_error
    # All are rational upper bounds for Euclidean norms on the unit circle.
    distance=Q(5,8)
    g0=3/distance
    g1=3/distance+3/distance**2
    g2=2/distance+6/distance**2+6/distance**3
    H2=8*g2+24*g1+12*g0
    assert H2==Q(87776,125)
    integral_error=H2/(3*N*N)  # four parameter intervals, each error <= H2/(12N²)
    target=2*I*pi_mid*f(a)
    defect=integral_approx-target
    target_error=2*f(a).norm1()*pi_error
    certificate_bound=integral_error+target_error
    assert defect.abs2() <= certificate_bound**2
    assert pi_lo > 3 and pi_hi < 4
    checks += 3
    return {"N_per_quarter":N,"status":"PASS","exact_assertions":checks,
            "point":complex_json(a),"f_at_point":complex_json(f(a)),
            "pi_midpoint":rational_json(pi_mid),
            "pi_interval":{"lower":rational_json(pi_lo),"upper":rational_json(pi_hi),
                           "radius":rational_json(pi_error)},
            "boundary_integral_trapezoid":complex_json(integral_approx),
            "target_with_pi_midpoint":complex_json(target),
            "defect":complex_json(defect),
            "defect_norm_squared":rational_json(defect.abs2()),
            "certified_euclidean_error_bound":rational_json(certificate_bound),
            "certified_error_bound_squared":rational_json(certificate_bound**2),
            "exact_squared_comparison":True,
            "bound_constants":{"distance_lower":rational_json(distance),
                              "H_second_derivative_upper":rational_json(H2),
                              "integral_quadrature_error":rational_json(integral_error),
                              "pi_normalization_error":rational_json(target_error)}}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path)
    args=parser.parse_args()
    # Exact fraction output can be long; this affects formatting only.
    if hasattr(sys,"set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    report={"format_version":1,
            "scope":"Exact finite illustrations and a rational quadrature certificate; not a formal iPRA or Lean proof.",
            "finite_identities":finite_identity_tests(),
            "affine_triangles":affine_triangle_tests(),
            "taylor":taylor_polynomial_tests(),
            "circle_cauchy":[circle_cauchy_certificate(64),circle_cauchy_certificate(128)]}
    result=json.dumps(report,indent=2,sort_keys=True)+"\n"
    if args.output:
        args.output.write_text(result,encoding="utf-8")
        print("PASS: exact validation; deterministic report written to",args.output)
    else:
        print(result,end="")


if __name__=="__main__":
    main()
