#!/usr/bin/env python3
"""Reproduce the numerical and exact checks in the accompanying article.

Requirements: Python 3.10+, mpmath, sympy.
Run: python verify_results.py --dps 60 --nodes 64 --output results_64.json
The quadrature is high-precision floating point, NOT interval arithmetic.
Increase both --dps and --nodes to check stability independently.
"""
from __future__ import annotations
import argparse
import json
import math
import time
from pathlib import Path
import mpmath as mp
import sympy as sp


def exact_coefficients(nmax: int = 12) -> tuple[list[sp.Expr], dict[str, bool]]:
    a = sp.symbols('a', real=True)
    ell = [sp.S.Zero] * (nmax + 1)
    ell[1] = sp.Rational(1, 2) - a
    for j in range(1, nmax // 2 + 1):
        ell[2*j] = -sp.bernoulli(2*j)/(2*j*sp.factorial(2*j)*(4**j-1))
    r = [sp.S.One]
    for n in range(1, nmax + 1):
        r.append(sp.expand(sum(j*ell[j]*r[n-j] for j in range(1, n+1))/n))
    c = [sp.expand(2**(k*(k+1)//2)*r[k]) for k in range(nmax + 1)]
    derivative = all(sp.expand(sp.diff(c[k], a) + 2**k*c[k-1]) == 0
                     for k in range(1, nmax+1))
    reflection = all(sp.expand(c[k].subs(a, 1-a) - (-1)**k*c[k]) == 0
                     for k in range(nmax+1))
    centered = all(c[k].subs(a, sp.Rational(1,2)) == 0 for k in range(1,nmax+1,2))
    assert derivative and reflection and centered
    return c, {'coefficient_derivative': derivative, 'reflection': reflection,
               'centered_odd_coefficients_vanish': centered}


class DyadicQuadrature:
    """One-cell quadrature; original Q integrals and W moments are separate."""
    def __init__(self, dps: int, nodes: int, max_order: int = 16) -> None:
        mp.mp.dps = dps
        self.dps, self.nodes = dps, nodes
        self.lam = mp.log(2)
        self.radius = math.ceil(math.sqrt(2*(dps+25)*math.log(10)/math.log(2))) + 3
        self.jmin, self.jmax = -max_order-self.radius, self.radius
        self.bernoulli = [mp.bernoulli(2*j)/(2*j*mp.factorial(2*j)*(mp.mpf(4)**j-1))
                          for j in range(1, dps//5+12)]
        xs, ws = mp.gauss_quadrature(nodes, 'legendre')
        self.data = []
        for xx, ww in zip(xs, ws):
            y, weight = (xx+1)/2, ww/2
            v = mp.power(2,y)
            lq = self.log_q(v)
            lh = self.log_h(v)
            amp = mp.exp(lq + lh + self.lam*(y*y-y)/2)
            qlogs = {0: lq}
            for j in range(-1,self.jmin-1,-1):
                qlogs[j] = qlogs[j+1] + mp.log(-mp.expm1(-mp.ldexp(v,j)))
            for j in range(1,self.jmax+1):
                # Direct positive-scale product avoids subtractive cancellation.
                qlogs[j] = self.log_q(mp.ldexp(v,j))
            cells = [(self.lam*(y+j), mp.ldexp(v,j), qlogs[j])
                     for j in range(self.jmin,self.jmax+1)]
            self.data.append((y,weight,amp,cells))

    def log_q(self, t: mp.mpf) -> mp.mpf:
        if t <= 0:
            raise ValueError('Q is evaluated only for t > 0')
        total = mp.mpf(0)
        cutoff = (self.dps+20)*mp.log(10)
        while t < cutoff:
            total += mp.log(-mp.expm1(-t))
            t *= 2
        return total

    def log_h(self, z: mp.mpf) -> mp.mpf:
        total = mp.mpf(0)
        while abs(z) > mp.mpf('0.025'):
            z /= 2
            total += mp.log(-mp.expm1(-z)/z)
        return total-z/2+mp.fsum(b*z**(2*j) for j,b in enumerate(self.bernoulli,1))

    def theta(self, rho: mp.mpf) -> mp.mpf:
        theta = rho - mp.floor(rho)
        vals=[]
        for y,weight,amp,_ in self.data:
            kernel=mp.fsum(mp.power(2,-(j+y+theta-mp.mpf('.5'))**2/2)
                          for j in range(-self.radius,self.radius+1))
            vals.append(weight*amp*kernel)
        return self.lam*mp.power(2,mp.mpf(1)/8)*mp.fsum(vals)

    def mellin_k(self, s: mp.mpf) -> mp.mpf:
        return mp.power(2,s*(s+1)/2)*self.theta(-s)

    def original_normalized_c(self, rho: mp.mpf, a: mp.mpf) -> mp.mpf:
        """C_rho / 2^[rho(rho-1)/2], using only the original Q-integral."""
        if a <= 0 or rho < 0:
            raise ValueError('Require a > 0 and rho >= 0')
        shift=self.lam*rho*(rho-1)/2
        vals=[]
        for _,weight,_,cells in self.data:
            vals.append(weight*mp.fsum(mp.exp(-rho*x-a*t+lq-shift)
                                       for x,t,lq in cells))
        return self.lam*mp.fsum(vals)

    def phase_solution(self, theta: mp.mpf, a: mp.mpf, slope: bool=False) -> mp.mpf:
        # Truncate well beyond both the product and exponential transition zones.
        center=math.floor(float(-mp.log(a,2)-theta))
        vals=[]
        for j in range(-self.radius-10, max(self.radius,center+self.radius)+1):
            t=mp.power(2,j+theta)
            val=mp.exp(-a*t+self.log_q(t))
            vals.append(a*t*val if slope else val)
        return self.lam*mp.fsum(vals)


def run(dps: int, nodes: int) -> dict:
    start=time.monotonic()
    cs,exact=exact_coefficients()
    q=DyadicQuadrature(dps,nodes)
    fmt=lambda x: mp.nstr(x,max(30,dps-10))
    k0=q.theta(mp.mpf(0))
    result={'precision_digits':dps,'quadrature_nodes':nodes,
            'dyadic_tail_radius':q.radius,'interval_certified':False,
            'versions':{'mpmath':mp.__version__,'sympy':sp.__version__},
            'exact_checks':exact,'coefficients':[str(x) for x in cs],
            'K0':fmt(k0),'centered':[], 'noncentered':[],
            'theta_relative_variation':{},'phase_solutions':[]}
    for m in (4,8,12,16):
        rho=mp.mpf(m)
        ratio=q.original_normalized_c(rho,mp.mpf('.5'))/k0
        p2=1-mp.power(2,-2*m)/9
        p4=p2+mp.mpf(248)/2025*mp.power(2,-4*m)
        p6=p4-mp.mpf(4806656)/2679075*mp.power(2,-6*m)
        result['centered'].append({'m':m,'ratio':fmt(ratio),
            'error_leading':fmt(abs(ratio-1)), 'error_through_c2':fmt(abs(ratio-p2)),
            'error_through_c4':fmt(abs(ratio-p4)), 'error_through_c6':fmt(abs(ratio-p6))})
    a_symbol=next(iter(cs[1].free_symbols))
    c_one=[mp.mpf(str(cc.subs(a_symbol,1).p))/mp.mpf(str(cc.subs(a_symbol,1).q))
           for cc in cs]
    for rho in map(mp.mpf,('8','8.25','8.5','12.75')):
        theta=q.theta(rho)
        ratio=q.original_normalized_c(rho,mp.mpf(1))/theta
        p4=mp.fsum(c_one[k]*mp.power(2,-k*rho) for k in range(5))
        result['noncentered'].append({'rho':fmt(rho),'a':'1','ratio':fmt(ratio),
                                      'error_through_c4':fmt(abs(ratio-p4))})
    for theta in map(mp.mpf,('0','.25','.5','.75')):
        result['theta_relative_variation'][str(theta)]=fmt(q.theta(theta)/k0-1)
        f1=q.phase_solution(theta,mp.mpf(1))
        norm=q.phase_solution(theta,mp.mpf('.5'))
        residual=f1-q.phase_solution(theta,mp.mpf('.5'))+q.phase_solution(theta,mp.mpf(1))
        # The equation at a=1 is f(1)=f(.5)-f(1).
        smalla=mp.power(2,-24)
        result['phase_solutions'].append({'theta':fmt(theta),'f_1':fmt(f1),
          'f_1_over_3':fmt(q.phase_solution(theta,mp.mpf(1)/3)),
          'normalization_error':fmt(abs(norm-q.lam)),
          'dyadic_equation_at_1_error':fmt(abs(residual)),
          'small_a':fmt(smalla),'small_a_slope':fmt(q.phase_solution(theta,smalla,True))})
    # Nontrivial dyadic residual, rather than the special a=1 identity alone.
    aa=mp.mpf('1.3'); th=mp.mpf('.27')
    residual=q.phase_solution(th,aa)-q.phase_solution(th,aa/2)+q.phase_solution(th,(aa+1)/2)
    result['generic_dyadic_residual']=fmt(abs(residual))
    result['canonical_f_1_over_3']=fmt(q.original_normalized_c(mp.mpf(0),mp.mpf(1)/3))
    result['elapsed_seconds']=round(time.monotonic()-start,3)
    return result


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dps',type=int,default=60)
    parser.add_argument('--nodes',type=int,default=64)
    parser.add_argument('--output',type=Path,default=Path('results.json'))
    args=parser.parse_args()
    if args.dps < 40 or args.nodes < 24:
        parser.error('Use at least 40 digits and 24 quadrature nodes.')
    result=run(args.dps,args.nodes)
    args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__':
    main()
