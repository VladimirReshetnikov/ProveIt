#!/usr/bin/env python3
"""Independent checks for audit_notes.tex.

Exact checks: pair-sum identity, power-sum ranks/Newton obstruction,
Beta degeneration moments, and low-degree quarter-parameter identities.
Numerical checks: coefficients of determinants of one-dimensional moment
integrals, using Gauss--Legendre quadrature. No Gamma quotient is used
for the expectation side. Finite quadrature residuals are diagnostics,
not interval certificates. Run python verify_gamma_cumulants.py.
"""
from __future__ import annotations
from collections import Counter, defaultdict
from itertools import permutations, product
from math import factorial
import argparse, json, pathlib, time
import mpmath as mp
import sympy as sp


def partitions(n, minimum=1):
    if n == 0:
        yield ()
    else:
        for k in range(minimum, n+1):
            for rest in partitions(n-k, k):
                yield (k,) + rest


def set_partitions(items):
    if not items:
        yield ()
        return
    first, *rest = items
    for part in set_partitions(rest):
        yield ((first,),) + part
        for j in range(len(part)):
            yield part[:j] + ((first,) + part[j],) + part[j+1:]


def exact_checks():
    count = 0
    for N in range(1,9):
        for degree in range(1,13):
            z = [(-1)**j*(j+2) for j in range(N)]
            ps = lambda k: sum(a**k for a in z)
            lhs = sum((z[i]+z[j])**degree for i in range(N)
                      for j in range(i+1,N))
            rhs = (N-2**(degree-1))*ps(degree)
            rhs += sum(sp.binomial(degree,a)*ps(a)*ps(degree-a)
                       for a in range(1,degree))/2
            assert lhs == rhs
            count += 1
    ranks = []
    # Products p_lambda, expanded independently in ordinary monomials.
    for N in range(1,6):
        for degree in range(1,N+2):
            lam = list(partitions(degree))
            mon = [v for v in lam if len(v)<=N]
            cols = []
            for row in lam:
                poly = {(0,)*N: sp.Integer(1)}
                for k in row:
                    new = defaultdict(int)
                    for ex,c in poly.items():
                        for j in range(N):
                            ne=list(ex); ne[j]+=k
                            new[tuple(ne)] += c
                    poly=new
                cols.append([poly.get(tuple(v)+(0,)*(N-len(v)),0)
                             for v in mon])
            matrix = sp.Matrix.hstack(*(sp.Matrix(c) for c in cols))
            rank=matrix.rank()
            expected=len(lam)-(degree==N+1)
            assert rank==expected
            count += 1
            ranks.append({'N':N,'degree':degree,'rank':rank,
                          'formal_coordinates':len(lam)})
    t=sp.symbols('t')
    f=1-3*t+2*t*t
    central=[]
    for k in range(1,5):
        pp=sp.Poly((f-sp.Rational(1,4))**k,t)
        val=sp.factor(sum(c*sp.rf(sp.Rational(3,2),e[0])/
                              sp.rf(4,e[0]) for e,c in pp.terms()))
        central.append(str(val)); count+=1
    assert central==['0','3/32','1/64','39/2048']
    assert sp.simplify((sp.Rational(32,3))**sp.Rational(3,2)/64
                      -2*sp.sqrt(6)/9)==0
    assert sp.Rational(136,16)+sp.Rational(64,8)==sp.Rational(33,2)
    count+=2
    return {'assertions':count,'power_sum_ranks':ranks,
            'beta_central_moments_1_to_4':central,
            'limiting_standardized_skewness':'2*sqrt(6)/9'}


def mul(a,b,limits):
    out=defaultdict(mp.mpf)
    for x,c in a.items():
        for y,d in b.items():
            z=tuple(i+j for i,j in zip(x,y))
            if all(z[i]<=limits[i] for i in range(len(z))):
                out[z]+=c*d
    return out


def permutation_sign(p):
    return -1 if sum(p[i]>p[j] for i in range(len(p))
                    for j in range(i+1,len(p)))%2 else 1


class IntegralMeasure:
    """Store integrand samples independently from claimed moment formulas."""
    def __init__(self,n,sigma,maxq,nodes):
        self.n=n; self.sigma=mp.mpf(sigma); self.N=2*n+2
        roots,weights=mp.gauss_quadrature(nodes,'legendre')
        intervals=[mp.mpf(x) for x in ('0','.25','.5','1','2','4','8','16','32','48')]
        self.samples=[]
        for lo,hi in zip(intervals,intervals[1:]):
            width=(hi-lo)/2; mid=(lo+hi)/2
            for root,wt in zip(roots,weights):
                x=mid+width*root; z=self.sigma+mp.j*x/2
                W=mp.exp(2*self.N*mp.re(mp.loggamma(z)))
                g=[mp.re(mp.polygamma(q,z)) for q in range(maxq+1)]
                base=[[width*wt*W*x**(2*r-1)*mp.sinh(k*mp.pi*x)
                       for k in range(1,n+1)] for r in range(1,n+1)]
                self.samples.append((g,base))
        self.cache={}

    def jet(self,orders):
        counter=Counter(orders); qs=tuple(sorted(counter))
        limits=tuple(counter[q] for q in qs)
        cachekey=(qs,limits)
        if cachekey in self.cache: return self.cache[cachekey]
        exps=list(product(*(range(k+1) for k in limits)))
        zero=(0,)*len(qs)
        matrix=[[{e:mp.mpf('0') for e in exps} for j in range(self.n)]
                for i in range(self.n)]
        for gs,base in self.samples:
            insertion={e:mp.fprod(gs[q]**a/mp.factorial(a)
                                 for q,a in zip(qs,e)) for e in exps}
            for r in range(self.n):
                for k in range(self.n):
                    for e,v in insertion.items(): matrix[r][k][e]+=base[r][k]*v
        det=defaultdict(mp.mpf)
        for perm in permutations(range(self.n)):
            term={zero:mp.mpf(permutation_sign(perm))}
            for i,j in enumerate(perm): term=mul(term,matrix[i][j],limits)
            for e,v in term.items(): det[e]+=v
        norm=det[zero]
        raw={e:v/norm*mp.fprod(mp.factorial(a) for a in e) for e,v in det.items()}
        self.cache[cachekey]=(qs,raw)
        return qs,raw

    def cumulant(self,orders):
        qs,raw=self.jet(orders)
        ans=mp.mpf('0')
        for part in set_partitions(tuple(range(len(orders)))):
            term=(-1)**(len(part)-1)*factorial(len(part)-1)
            for block in part:
                c=Counter(orders[i] for i in block)
                term*=raw[tuple(c[q] for q in qs)]
            ans+=term
        return ans

    def centered_moment(self,orders):
        qs,raw=self.jet(orders)
        mus={q:raw[tuple(int(q==qq) for qq in qs)] for q in qs}
        ans=mp.mpf('0')
        for mask in range(1<<len(orders)):
            selected=Counter(orders[i] for i in range(len(orders)) if mask>>i&1)
            term=raw[tuple(selected[q] for q in qs)]
            for i,q in enumerate(orders):
                if not (mask>>i&1):term*=-mus[q]
            ans+=term
        return ans


def predicted(n,sigma,orders):
    N=2*n+2; sigma=mp.mpf(sigma); r=len(orders)
    assert sum(q+1 for q in orders)<=N
    if r==1:
        q=orders[0]
        return ((N-2**q)*mp.polygamma(q,2*sigma)
                -(mp.digamma(N*sigma) if q==0 else 0))/2
    if r==2:
        p,q=orders
        return (mp.polygamma(p+q+1,2*sigma)
                -(mp.polygamma(1,N*sigma) if p==q==0 else 0))/4
    if any(orders):return mp.mpf('0')
    return -mp.polygamma(r-1,N*sigma)/2**r


def numeric_suite(dps,nodes):
    mp.mp.dps=dps
    result=[]
    cases=[(1,'0.25',[(2,),(3,),(0,2),(0,1),(0,0,1),(0,0,0),(0,0,0,0)]),
           (1,'0.4',[(2,),(0,2),(0,0,1),(0,0,0,0)]),
           (2,'0.333333333333333333333333333333',[(5,),(1,3),(2,2),(0,1,2),(1,1,1),(0,0,0,1)])]
    for n,sigma,patterns in cases:
        measure=IntegralMeasure(n,sigma,max(max(p) for p in patterns),nodes)
        for pat in patterns:
            actual=measure.cumulant(pat); expected=predicted(n,sigma,pat)
            residual=abs(actual-expected)
            result.append({'n':n,'sigma':sigma,'orders':pat,
                           'weight':sum(q+1 for q in pat),
                           'integral_cumulant':mp.nstr(actual,dps-5),
                           'formula':mp.nstr(expected,dps-5),
                           'absolute_residual':mp.nstr(residual,8),
                           'scaled_residual':mp.nstr(residual/max(1,abs(expected)),8)})
    # A direct excluded skewness diagnostic, deliberately outside theorem.
    sharp=[]
    for sigma in ('0.02','0.005'):
        # Use x=2sigma*y in dedicated adaptive one-dimensional quadrature.
        s=mp.mpf(sigma)
        normalizer=4*mp.pi**2*mp.gamma(2*s)**6/mp.gamma(4*s)
        mu=mp.polygamma(1,2*s); varscale=mp.sqrt(mp.polygamma(3,2*s))
        def integrand(y):
            x=2*s*y; z=s*(1+mp.j*y)
            density=2*s*x*mp.sinh(mp.pi*x)*mp.exp(8*mp.re(mp.loggamma(z)))/normalizer
            X=(2*mp.re(mp.polygamma(1,z))-2*mu)/varscale
            return density*X**3
        val=mp.quad(integrand,[0,1,3,10,30,100,mp.inf])
        sharp.append({'sigma':sigma,'third_standardized_moment':mp.nstr(val,dps-5),
                      'small_sigma_limit':mp.nstr(2*mp.sqrt(6)/9,dps-5)})
    assert max(mp.mpf(r['scaled_residual']) for r in result)<mp.mpf('1e-22')
    return {'dps':dps,'Gauss_Legendre_nodes_per_interval':nodes,
            'finite_intervals':[0,.25,.5,1,2,4,8,16,32,48],
            'checks':result,'excluded_skewness_diagnostics':sharp,
            'largest_scaled_residual':mp.nstr(max(mp.mpf(r['scaled_residual']) for r in result),8)}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--dps',type=int,default=36)
    parser.add_argument('--nodes',type=int,default=56)
    parser.add_argument('--output',default='gamma_cumulant_checks.json')
    args=parser.parse_args();start=time.time()
    out={'exact':exact_checks(),'numerical':numeric_suite(args.dps,args.nodes)}
    out['elapsed_seconds']=round(time.time()-start,2)
    pathlib.Path(args.output).write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'exact_assertions':out['exact']['assertions'],
                      'numerical_checks':len(out['numerical']['checks']),
                      'largest_scaled_residual':out['numerical']['largest_scaled_residual'],
                      'elapsed_seconds':out['elapsed_seconds'],'output':args.output}))

if __name__=='__main__':main()
