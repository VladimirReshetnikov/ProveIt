#!/usr/bin/env python3
"""Finite regression checks; not a proof of the asymptotic theorem.

The huge-height test works with integer bin counts, not individual ordinates.
Decimal logarithms are numerical; all greedy allocation is integer arithmetic.
The second test checks Fourier interpolation numerically (requires numpy).
"""
from decimal import Decimal, localcontext, ROUND_FLOOR
from functools import lru_cache
import json, math, random
from pathlib import Path
import numpy as np

D, H, JMAX = 64, 512, 8
# a=1, c=1, C=8 for the test; conservative parameter choices.
def h(i): return H * 2**(i-1)
def M(i): return 100*i*i
def R(i): return (M(i)+1)*M(i)*h(i)
with localcontext() as ctx:
    ctx.prec = 400
    T = {i: int((Decimal(D)*(Decimal(i)-Decimal('0.25'))).exp()) for i in range(1,JMAX+2)}
assert all(T[i] >= 4*(R(i+1)+h(i+1)+2) for i in range(1,JMAX+1))
assert H >= 64*8
assert D >= 16*(1+math.log(2)+1)

@lru_cache(maxsize=None)
def count(x):
    """N_<(x) at integer x for a clustered model.
    Put jumps at half-integers. Perturb floor(x log(x+2)) by O(log x).
    """
    if x == 0: return 0
    with localcontext() as ctx:
        ctx.prec = len(str(x))+45
        z=Decimal(x+2).ln()
        return int(Decimal(x)*z) + (-1 if (x//H)%2 else 1)*int(z/4)

def run_bin(j, x):
    assert x%h(j)==0
    residual=[]
    for y in range(x,x+h(j),h(1)):
        n=count(y+h(1))-count(y)
        assert n>=0
        residual.append(0 if y<R(1) else n)
    saturation_checks=0
    assigned=0
    for i in range(1,j+1):
        if i>1: residual=[residual[k]+residual[k+1] for k in range(0,len(residual),2)]
        nxt=[]
        for k,n in enumerate(residual):
            y=x+k*h(i)
            take=min(n,D*h(i)) if y>=R(i) else 0
            if y>=T[i+1]//2+1:
                assert take==D*h(i),(j,i,y,n)
                saturation_checks+=1
            assert 0<=take<=n and take<=D*h(i)
            assigned+=take
            nxt.append(n-take)
        residual=nxt
    assert len(residual)==1
    return residual[0],saturation_checks,assigned

def check_layering():
    rng=random.Random(20261127)
    cases=checks=cover=above=0
    for j in range(1,JMAX+1):
        probes={0,R(1),R(j),T[j],T[j]//2,2*T[j],T[j+1]}
        if j>1: probes|={T[j-1]-1,T[j-1]+1,T[j-1]//2}
        probes|={rng.randrange(T[j]+1) for _ in range(6)}
        for p in probes:
            x=p//h(j)*h(j)
            rem,n,assigned=run_bin(j,x)
            checks+=n; cases+=1
            if x<=T[j]:
                assert rem==0,(j,x,rem)
                cover+=1
            elif x>=T[j+1]//2+1:
                # All layers saturated; the model generally retains carry here.
                above+=int(rem>0)
    return dict(levels=JMAX, cases=cases, coverage_checks=cover,
                saturation_checks=checks, high_bins_with_positive_carry=above,
                largest_height_digits=len(str(T[JMAX+1])), parameters=dict(D=D,H=H))

def check_interpolation():
    rng=random.Random(27112026)
    out=[]
    for eta in (1.0,0.25,1/9,0.04):
        m=math.ceil(100/eta); c=m+1; delta=1.0
        r=m//2
        # One point per phase bin, with near-extreme offsets.
        ks=sorted(set([c+i for i in range(16)]+[c+40,c+91]))
        pos=np.array([k+(r+(0.0001 if i%2==0 else 0.9999))/m for i,k in enumerate(ks)])
        lam=np.concatenate((-pos[::-1],pos))
        def f(x): return np.sinc(x)*np.sinc(eta*x/np.pi)
        mat=f(lam[:,None]-lam[None,:]); b=f(lam)
        coeff=np.linalg.solve(mat,-b)
        residual=float(np.max(np.abs(mat@coeff+b)))
        norm=float(np.sum(np.abs(coeff)))
        off=float(np.linalg.norm(mat-np.eye(len(lam)),1))
        bnorm=float(np.linalg.norm(b,1))
        assert off<0.25 and bnorm<0.25 and norm<1/3 and residual<1e-12
        assert np.max(np.abs(coeff-coeff[::-1]))<1e-12
        ts=np.linspace(-math.pi-eta, math.pi+eta, 301)
        q=1+np.exp(-1j*ts[:,None]*lam[None,:])@coeff
        assert np.max(np.abs(q.imag))<1e-12 and np.min(q.real)>2/3
        out.append(dict(eta=eta,points=len(lam),column_error=off,b_l1=bnorm,
                        coefficient_l1=norm,linear_residual=residual,
                        min_sampled_multiplier=float(q.real.min())))
    return out

if __name__=='__main__':
    results=dict(status='passed', caveat='Finite regression checks only; decimal and Fourier calculations are numerical.',
                 layering=check_layering(), interpolation=check_interpolation())
    path=Path(__file__).with_name('results.json')
    path.write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))
