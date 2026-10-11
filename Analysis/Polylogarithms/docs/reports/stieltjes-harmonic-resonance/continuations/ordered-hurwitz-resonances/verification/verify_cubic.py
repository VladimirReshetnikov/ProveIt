#!/usr/bin/env python3
"""Independent numerical diagnostic for the cubic coincident finite part.

T(s,s,s) is evaluated from the Mellin integral of Li_s(exp(-t))^2,
using its convergent Jonquiere expansion on (0,1) and an exponentially
convergent integral on (1,infinity). No Hurwitz product integral is used
in that evaluation. This is floating-point evidence, not interval proof.
"""
import argparse
import json
from functools import lru_cache
import mpmath as mp

P = 3

def add(a,b):
    return [a[j]+b[j] for j in range(P+1)]

def scale(a,b):
    return [b*x for x in a]

def mul(a,b):
    return [sum(a[j]*b[n-j] for j in range(n+1)) for n in range(P+1)]

def shift(a):
    return [mp.mpf(0)]+a[:P]

def invlinear(a,b):
    return [(-b)**j/mp.mpf(a)**(j+1) for j in range(P+1)]

def tay(f):
    return list(mp.taylor(f,0,P))

def diagonal_tornheim_jets(dps=45, terms=64):
    mp.mp.dps=dps
    gamma_minus=tay(lambda s:mp.gamma(1-s))
    rgamma_plus=tay(lambda s:mp.rgamma(1+s))
    c=[]
    for k in range(terms+1):
        c.append(scale(tay(lambda s,k=k:mp.zeta(s-k)),(-1)**k/mp.factorial(k)))
    r=mul(shift(mul(gamma_minus,gamma_minus)),invlinear(-2,3))
    r=add(r,mul(gamma_minus,c[1]))
    for k in range(terms+1):
        if k!=1:
            r=add(r,scale(mul(shift(mul(gamma_minus,c[k])),invlinear(k-1,2)),2))
    r=add(r,mul(c[0],c[0]))
    for q in range(1,terms+1):
        cq=[mp.mpf(0)]*(P+1)
        for k in range(q+1):
            cq=add(cq,mul(c[k],c[q-k]))
        r=add(r,mul(shift(cq),invlinear(q,1)))

    logn=[mp.log(n) for n in range(1,4*dps+20)]
    @lru_cache(maxsize=None)
    def tail_coeff(t):
        z=mp.exp(-t)
        l0=z/(1-z)
        l1=mp.mpf(0)
        l2=mp.mpf(0)
        zn=z
        for ln in logn:
            l1-=ln*zn
            l2+=ln**2*zn
            zn*=z
        lt=mp.log(t)
        return (l0*l0/t,(lt*l0*l0+2*l0*l1)/t,
                (lt*lt*l0*l0/2+2*lt*l0*l1+l1*l1+l0*l2)/t)
    endpoint=mp.mpf(2*dps+20)
    pieces=[mp.mpf(x) for x in (1,2,4,8,16,32)]+[endpoint]
    ic=[mp.quad(lambda t,j=j:tail_coeff(t)[j],pieces) for j in range(3)]
    r=add(r,[mp.mpf(0)]+ic)
    coeff=mul(r,rgamma_plus)
    return [mp.factorial(j)*coeff[j] for j in range(4)]

def psi_cube_finite_part():
    gamma=mp.euler
    zetas=[mp.zeta(k) for k in range(2,4*mp.mp.dps+20)]
    def regular(x):
        if x<mp.mpf('0.25'):
            # r=(psi(1+x)+gamma-zeta(2)*x)/x^2, with no subtraction.
            r=mp.polyval([(-1)**(k+1)*zetas[k-1] for k in range(len(zetas)-1,1,-1)],x)
            q=zetas[0]+x*r
            d=-gamma+x*q
            return 3*r+6*gamma*q-3*x*q*q+d**3
        d=mp.digamma(1+x)
        return 3*(d+gamma-zetas[0]*x)/(x*x)-3*(d*d-gamma*gamma)/x+d**3
    return mp.quad(regular,[0,mp.mpf('0.25'),1])+mp.mpf('0.5')+3*gamma

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--dps',type=int,default=45)
    ap.add_argument('--terms',type=int,default=64)
    ap.add_argument('--tolerance',default='1e-28')
    args=ap.parse_args()
    if args.dps < 10 or args.terms < 1:
        ap.error('--dps must be at least 10 and --terms at least 1')
    jets=diagonal_tornheim_jets(args.dps,args.terms)
    g=mp.euler
    ell=mp.log(2*mp.pi)
    g1=mp.stieltjes(1)
    g2=mp.stieltjes(2)
    z2=mp.zeta(2)
    z3=mp.zeta(3)
    zp2=mp.diff(mp.zeta,2)
    expected=[mp.mpf(1)/3,ell,3*ell**2-2*g**2-4*g1+z2]
    q=jets[3]+9*g**3+18*g*g*ell+30*g*g1+36*ell*g1+12*g2-9*ell**3-3*g*z2/2-9*ell*z2-3*z2/2-8*z3-3*zp2/2
    direct=psi_cube_finite_part()
    result={'dps':args.dps,'jonquiere_terms':args.terms,
            'tornheim_diagonal_derivatives':[mp.nstr(x,args.dps) for x in jets],
            'lower_jet_residuals':[mp.nstr(jets[j]-expected[j],8) for j in range(3)],
            'psi_cube_finite_part_direct':mp.nstr(direct,args.dps),
            'psi_cube_from_tornheim':mp.nstr(-q,args.dps),
            'absolute_residual':mp.nstr(abs(q+direct),8),
            'diagnostic_tolerance':args.tolerance,
            'diagnostic_passed':bool(max([abs(q+direct)]+[abs(jets[j]-expected[j]) for j in range(3)])<mp.mpf(args.tolerance)),
            'status':'floating-point diagnostic; not an interval enclosure'}
    print(json.dumps(result,indent=2))
    if not result['diagnostic_passed']:
        raise SystemExit('Numerical residual exceeded the stated diagnostic tolerance.')

if __name__=='__main__':
    main()
