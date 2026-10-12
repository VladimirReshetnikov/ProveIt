#!/usr/bin/env python3
"""Exact certificate replay plus independent high-precision diagnostics.

Requires mpmath and sympy. Numerical residuals are not interval certificates.
Usage: python verify_bilinear_tails.py [output.json]
"""
from functools import lru_cache
import json
from pathlib import Path
import sys

import mpmath as mp
import sympy as sp

mp.mp.dps = 45
records = []


def record(name, lhs, rhs, tolerance=mp.mpf("1e-36")):
    residual = abs(lhs - rhs)
    scale = max(1, abs(lhs), abs(rhs))
    assert residual < tolerance * scale, (name, mp.nstr(residual, 12))
    records.append({"name": name, "absolute_residual": mp.nstr(residual, 12),
                    "lhs": mp.nstr(lhs, 30), "rhs": mp.nstr(rhs, 30)})


def ell(z):
    return mp.log(2) / 2 + mp.loggamma((z + 1) / 2) - mp.loggamma(z / 2)


def h(z):
    return mp.exp(ell(z))


def beta(s, z):
    if s == 1:
        return (mp.digamma((z + 1) / 2) - mp.digamma(z / 2)) / 2
    return mp.power(2, -s) * (mp.zeta(s, z / 2) - mp.zeta(s, (z + 1) / 2))


def tau(s, z):
    return mp.exp(s * ell(z)) * beta(s, z)


def potential(s, z):
    return (mp.exp(s * mp.log(z)) - mp.exp(s * mp.log(z - 1))) * mp.exp(-2*s*ell(z))


def exact_certificates():
    e, f, r, c, qm, qp, sm, ss, sp1 = sp.symbols("e f r c qm qp sm ss sp1", nonzero=True)
    pn, pnext = c * qm * ss * sm, c * qp * sp1 * ss
    for t in (1, -1):
        aa, bb, ap, bp = qp * ss, t * qp * sp1, qm * sm, t * qm * ss
        current = (aa + bb)*e*f + aa*r/qp*e + bb*r/pnext*f
        previous = t*((ap + bp)*e*f + ap*r/pn*f + bp*r/qm*e)
        target = ((aa + bb) - t*(ap + bp))*e*f
        assert sp.factor(current - previous - target) == 0
    n, x, y = sp.symbols("n x y")
    aa, bb = (n+x)*(n+y+1), (n+y)*(n+x+1)
    assert sp.expand((aa+bb)-(aa+bb).subs(n,n-1)-2*(2*n+x+y)) == 0
    assert sp.expand(aa-bb-(x-y)) == 0
    assert sp.factor((x/y*sp.Symbol('D')-y/x*sp.Symbol('E'))/(2*(x-y))
                     -(x*x*sp.Symbol('D')-y*y*sp.Symbol('E'))/(2*x*y*(x-y))) == 0
    return 5


exact_count = exact_certificates()

cases = [
    (mp.mpf("1.3"), mp.mpf("2.1"), mp.mpf("0.6"), mp.mpf("1.1")),
    (mp.mpf("-0.7"), mp.mpf("1.8"), mp.mpf("0.5"), mp.mpf("0.9")),
    (mp.mpc("0.7", "0.2"), mp.mpc("1.4", "-0.3"),
     mp.mpc("0.8", "0.1"), mp.mpc("1.2", "-0.2")),
    (mp.mpf("-0.3"), mp.mpf("-0.2"), mp.mpf("0.4"), mp.mpf("1.2")),
]
for i, (p, q, a, b) in enumerate(cases):
    N = 35
    us = [tau(p, n+a+1) for n in range(-1,N+2)]
    vs = [tau(q, n+b+1) for n in range(-1,N+2)]
    plus = mp.fsum((potential(p,n+a+1)+potential(q,n+b+1))*us[n+1]*vs[n+1]
                   for n in range(N+1))
    minus = mp.fsum((-1)**n*(potential(p,n+a+1)-potential(q,n+b+1))*us[n+1]*vs[n+1]
                    for n in range(N+1))
    lower_plus = us[0]*vs[1]+us[1]*vs[0]
    lower_minus = us[0]*vs[1]-us[1]*vs[0]
    upper_plus = us[N+1]*vs[N+2]+us[N+2]*vs[N+1]
    upper_minus = us[N+1]*vs[N+2]-us[N+2]*vs[N+1]
    record(f"finite symmetric case {i}",plus,lower_plus-upper_plus)
    record(f"finite antisymmetric case {i}",minus,lower_minus+(-1)**N*upper_minus)


def D(z):
    return 2*beta(1,z)-1/z


def K(x,y):
    if x == y:
        return D(x)**2/2+D(x)/x+mp.diff(D,x)/2
    return D(x)*D(y)/2+(x*x*D(x)-y*y*D(y))/(2*x*y*(x-y))


def M(x,y):
    return (x/y*D(x)+y/x*D(y)-(2*x*y-x-y)*D(x)*D(y))/2


for i,(x,y) in enumerate([(mp.mpf(1),mp.mpf(2)),(mp.mpf("0.7"),mp.mpf("1.9")),
                          (mp.mpc("1.2","0.3"),mp.mpc("0.8","-0.2"))]):
    record(f"D ordinary kernel {i}",mp.nsum(lambda n:(2*n+x+y)*D(n+x)*D(n+y),[0,mp.inf]),M(x,y))
    record(f"D alternating kernel {i}",mp.nsum(lambda n:(-1)**n*D(n+x)*D(n+y),[0,mp.inf]),K(x,y))
record("D confluent kernel",mp.nsum(lambda n:(-1)**n*D(n+1)**2,[0,mp.inf]),K(mp.mpf(1),mp.mpf(1)))
record("D explicit diagonal",K(mp.mpf(1),mp.mpf(1)),2*mp.log(2)**2-mp.pi**2/12)
record("D explicit adjacent",K(mp.mpf(1),mp.mpf(2)),1-2*mp.log(2)**2)

p,q,x,y=2,3,mp.mpf("0.8"),mp.mpf("1.7")
def Dp(p,z):
    return beta(p,z)-beta(p,z+1)
record("D independent orders 2,3",
       mp.nsum(lambda n:(-1)**n*Dp(p,n+x)*Dp(q,n+y),[0,mp.inf]),
       (-1)**(p+q-2)*mp.diff(lambda xx,yy:K(xx,yy),(x,y),(p-1,q-1))/
       (mp.factorial(p-1)*mp.factorial(q-1)))

for i,(a,b) in enumerate([(mp.mpf("0.7"),mp.mpf("2.2")),
                          (mp.mpf(1),mp.mpf(2)),
                          (mp.mpc("0.9","0.1"),mp.mpc("1.6","-0.15"))]):
    record(f"pure Gamma increment {i}",
           mp.nsum(lambda n:(h(n+b)-h(n+a))**2/(h(n+a)*h(n+b)),[1,mp.inf]),
           (h(b)-h(a))*(h(b+1)-h(a+1)))
record("Gamma increment explicit value",(h(2)-h(1))*(h(3)-h(2)),3-mp.pi/2-4/mp.pi)


@lru_cache(maxsize=None)
def Tjet(r,z):
    return h(z)/2*mp.fsum(mp.binomial(r,j)*(ell(z)-mp.log(2))**(r-j)*(-1)**j*
                         (mp.stieltjes(j,z/2)-mp.stieltjes(j,(z+1)/2)) for j in range(r+1))


def Jjet(r,z):
    return (z*(mp.log(z)-2*ell(z))**r-(z-1)*(mp.log(z-1)-2*ell(z))**r)/h(z)**2


z=mp.mpf("1.5")
for r in range(3):
    def integrand(t):
        base=mp.exp(-z*t)/(1+mp.exp(-t))
        v=ell(z)+mp.log(t)+mp.euler
        return base*(1 if r==0 else v if r==1 else v*v-mp.zeta(2))
    integral=h(z)*mp.quad(integrand,[0,1,mp.inf])
    record(f"Stieltjes jet {r} versus independent Laplace integral",Tjet(r,z),integral)

# The mixed r=s=1 finite identity is checked with independently constructed
# Stieltjes coefficients, without differentiating the telescoper in code.
a,b,N=mp.mpf("0.7"),mp.mpf("1.2"),5
terms_plus=[];terms_minus=[]
for n in range(N+1):
    z,w=n+a+1,n+b+1
    xx=Jjet(0,z)*Tjet(1,z)*Tjet(1,w)+Jjet(1,z)*Tjet(0,z)*Tjet(1,w)
    yy=Jjet(0,w)*Tjet(1,z)*Tjet(1,w)+Jjet(1,w)*Tjet(1,z)*Tjet(0,w)
    terms_plus.append(xx+yy);terms_minus.append((-1)**n*(xx-yy))
lower_plus=Tjet(1,a)*Tjet(1,b+1)+Tjet(1,a+1)*Tjet(1,b)
lower_minus=Tjet(1,a)*Tjet(1,b+1)-Tjet(1,a+1)*Tjet(1,b)
upper_plus=Tjet(1,N+a+1)*Tjet(1,N+b+2)+Tjet(1,N+a+2)*Tjet(1,N+b+1)
upper_minus=Tjet(1,N+a+1)*Tjet(1,N+b+2)-Tjet(1,N+a+2)*Tjet(1,N+b+1)
record("independent Stieltjes 1,1 finite symmetric",mp.fsum(terms_plus),lower_plus-upper_plus)
record("independent Stieltjes 1,1 finite antisymmetric",mp.fsum(terms_minus),lower_minus+(-1)**N*upper_minus)

# A nontrivial point on p+q=0 tests the actual ordinary contact, not merely
# a limit of the endpoint continuation.
p,a,b=mp.mpf(1),mp.mpf("0.6"),mp.mpf("1.1")
contact_sum=mp.nsum(lambda n:(potential(p,n+a+1)+potential(-p,n+b+1))*
                   tau(p,n+a+1)*tau(-p,n+b+1),[0,mp.inf])
contact_rhs=tau(p,a)*tau(-p,b+1)+tau(p,a+1)*tau(-p,b)-mp.mpf("0.5")
record("ordinary p+q=0 half contact",contact_sum,contact_rhs)

out={"precision_decimal_digits":mp.mp.dps,"exact_symbolic_assertions":exact_count,
     "numerical_diagnostics":len(records),
     "numerical_claim":"High-precision diagnostics only; no interval certification.",
     "checks":records}
path=Path(sys.argv[1] if len(sys.argv)>1 else "bilinear_verification.json")
path.write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps({"exact":exact_count,"diagnostics":len(records),"precision":mp.mp.dps,
                  "largest_residual":max(float(r['absolute_residual']) for r in records),
                  "output":str(path)}))
