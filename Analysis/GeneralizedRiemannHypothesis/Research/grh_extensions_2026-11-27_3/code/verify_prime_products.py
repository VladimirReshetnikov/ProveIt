#!/usr/bin/env python3
"""Exact checks for the finite-population theorem; illustrative convergence data.

The proof is in prime_product_limits.tex. Enumeration, factorial moments, and
binomial approximations are computed separately here. No GRH verification is
performed and finite examples do not prove an asymptotic theorem.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, product
from math import comb, factorial
from pathlib import Path
import json
import math

ROOT = Path(__file__).resolve().parents[1]

def group(moduli):
    elems = list(product(*(range(n) for n in moduli)))
    ix = {x: i for i, x in enumerate(elems)}
    add = [[ix[tuple((x[k]+y[k]) % n for k,n in enumerate(moduli))]
            for y in elems] for x in elems]
    return elems, add

def conv(a, b, add):
    out = [F(0) for _ in a]
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b):
                if y: out[add[i][j]] += x*y
    return out

def elementary(defects, add):
    d = len(add)
    coeffs = [[F(1)] + [F(0)]*(d-1)]
    for x in defects:
        delta = [F(0)]*d
        delta[0] -= 1
        delta[x] += 1
        nxt = [row[:] for row in coeffs] + [[F(0)]*d]
        for j,row in enumerate(coeffs):
            term = conv(row,delta,add)
            nxt[j+1] = [a+b for a,b in zip(nxt[j+1],term)]
        coeffs = nxt
    return coeffs

def falling(n,j):
    if j>n: return 0
    v=1
    for i in range(j): v *= n-i
    return v

def weighted(coeffs, weights):
    return [sum((w*c[g] for w,c in zip(weights,coeffs)), F(0))
            for g in range(len(coeffs[0]))]

def compositions(total, parts):
    if parts==1:
        yield (total,)
    else:
        for j in range(total+1):
            for tail in compositions(total-j,parts-1):
                yield (j,)+tail

def exact_checks():
    cases=0
    subsets=0
    worst_ratio=F(0)
    for moduli in [(2,), (3,), (4,), (2,2), (5,)]:
        elems,add=group(moduli)
        d=len(elems)
        for m in range(2,10):
            for t in range(m//2+1):
                for counts in compositions(t,d-1):
                    defects=[x for x,c in enumerate(counts,1) for _ in range(c)]
                    labels=[0]*(m-t)+defects
                    coeffs=elementary(defects,add)
                    for h in range(1,m//2+1):
                        hist=[0]*d
                        for subset in combinations(range(m),h):
                            g=0
                            for i in subset: g=add[g][labels[i]]
                            hist[g]+=1
                        subsets += comb(m,h)
                        actual=[F(v,comb(m,h)) for v in hist]
                        moments=weighted(coeffs,[F(falling(h,j),falling(m,j)) for j in range(t+1)])
                        assert actual==moments
                        u=F(h,m)
                        independent=weighted(coeffs,[u**j for j in range(t+1)])
                        second=weighted(coeffs,[j*(j-1)*u**j for j in range(t+1)])
                        correction=(F(1,2*h)-F(1,2*m))
                        residual=sum(abs(actual[g]-independent[g]+correction*second[g]) for g in range(d))
                        bound=sum((F(2*j**4,h*h)*comb(t,j)*(2*u)**j for j in range(t+1)),F(0))
                        assert residual<=bound
                        if bound: worst_ratio=max(worst_ratio,residual/bound)
                        assert sum(actual)==sum(independent)==1
                        assert sum(second)==0
                        cases+=1
    ratio_cases=0
    for m in range(2,81):
        for h in range(1,m//2+1):
            for j in range(m//2+1):
                u=F(h,m)
                r=F(falling(h,j),falling(m,j))/u**j
                assert 0 <= 1-r <= F(j*(j-1),h)
                err=abs(r-1+F(j*(j-1),2)*(F(1,h)-F(1,m)))
                assert err<=F(2*j**4,h*h)
                ratio_cases+=1
    return dict(population_and_quota_cases=cases, independently_enumerated_subsets=subsets,
                exact_ratio_inequalities=ratio_cases, max_remainder_to_certified_bound=float(worst_ratio),
                status="all exact assertions passed")

def hypergeometric_residues(m,h,t,mod):
    """Exact integer count, one recurrence across possible intersection sizes."""
    lo=max(0,h-(m-t))
    hi=min(h,t)
    cur=comb(t,lo)*comb(m-t,h-lo)
    totals=[0]*mod
    for j in range(lo,hi+1):
        totals[j%mod]+=cur
        if j<hi:
            num=cur*(t-j)*(h-j)
            den=(j+1)*(m-t-h+j+1)
            assert num%den==0
            cur=num//den
    denominator=comb(m,h)
    assert sum(totals)==denominator
    return [F(v,denominator) for v in totals]

def cyclic_bernoulli(t,u,d):
    den=u.denominator
    num=u.numerator
    totals=[0]*d
    for j in range(t+1):
        totals[j%d] += comb(t,j)*num**j*(den-num)**(t-j)
    return [F(v,den**t) for v in totals]

def convergence_data():
    _,add=group((4,))
    diff=[F(-1),F(1),F(0),F(0)]
    diff2=conv(diff,diff,add)
    cp=[(1+(-1)**j*math.exp(-2)+2*math.exp(-1)*math.cos(1-math.pi*j/2))/4 for j in range(4)]
    cp_first=[-.5*v for v in conv(diff2,cp,add)]
    rows=[]
    for h in [16,32,64,128,256,512,1024]:
        m=h*h; t=h; u=F(1,h)
        actual=hypergeometric_residues(m,h,t,4)
        independent=cyclic_bernoulli(t,u,4)
        second=[v*t*(t-1)*u*u for v in conv(diff2,cyclic_bernoulli(t-2,u,4),add)]
        c=F(1,2*h)-F(1,2*m)
        corrected=[independent[j]-c*second[j] for j in range(4)]
        rows.append(dict(h=h,m=m,defects=t,
                         l1_bernoulli_error=float(sum(abs(a-b) for a,b in zip(actual,independent))),
                         l1_corrected_error=float(sum(abs(a-b) for a,b in zip(actual,corrected))),
                         h_scaled_error=[float(h*(a-b)) for a,b in zip(actual,independent)],
                         normalized_exact_probabilities=[float(4*x) for x in actual]))
    # A correlated pair of quadratic signs. Character inversion reduces each
    # coefficient to an independently computed hypergeometric parity law.
    v4=[]
    rates={(1,0):.5,(0,1):.25,(1,1):.75}
    for h in [16,64,256]:
        m=h*h
        counts={(1,0):h//2,(0,1):h//4,(1,1):3*h//4}
        coeff={}
        for chi in [(0,0),(0,1),(1,0),(1,1)]:
            t=sum(n for x,n in counts.items() if (chi[0]*x[0]+chi[1]*x[1])%2)
            parity=hypergeometric_residues(m,h,t,2)
            coeff[chi]=parity[0]-parity[1]
        dist=[]
        for s,t in [(0,0),(0,1),(1,0),(1,1)]:
            val=sum(((-1)**(i*s+j*t)*c for (i,j),c in coeff.items()),F(0))/4
            dist.append(float(val))
        v4.append(dict(h=h,exact_probabilities=dist))
    v4limit=[]
    for s,t in [(0,0),(0,1),(1,0),(1,1)]:
        v4limit.append((1+(-1)**s*math.exp(-2*1.25)+(-1)**t*math.exp(-2*1.0)+(-1)**(s+t)*math.exp(-2*.75))/4)
    return dict(cyclic_four_at_rate_one=dict(limit=cp,first_correction=cp_first,rows=rows),
                klein_four=dict(rates={str(k):v for k,v in rates.items()},limit=v4limit,rows=v4))

def figures(data):
    import numpy as np
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'axes.spines.top':False,'axes.spines.right':False})
    fig,ax=plt.subplots(1,2,figsize=(10.8,4.0),layout='constrained')
    lam=np.linspace(0,5,501)
    colors=['#143d59','#007f85','#c47722','#94425b']
    for j,c in enumerate(colors):
        y=1+(-1)**j*np.exp(-2*lam)+2*np.exp(-lam)*np.cos(lam-np.pi*j/2)
        ax[0].plot(lam,y,label=f'Fibre {j}',color=c,lw=1.9)
    ax[0].axhline(1,color='#999999',ls='--',lw=.8)
    ax[0].set(xlabel='Expected sampled defects, λ',ylabel='Normalized limiting count',title='Four-fibre Poisson transition')
    ax[0].legend(frameon=False,ncol=2)
    rows=data['cyclic_four_at_rate_one']['rows']
    h=np.array([x['h'] for x in rows])
    err=np.array([x['l1_bernoulli_error'] for x in rows])
    corr=np.array([x['l1_corrected_error'] for x in rows])
    ax[1].loglog(h,err,'o-',label='Independent defect model',color=colors[0])
    ax[1].loglog(h,corr,'s-',label='With finite-population correction',color=colors[1])
    ax[1].loglog(h,err[0]*h[0]/h,'--',color='#aaaaaa',lw=.8,label='Reference slope −1')
    ax[1].loglog(h,corr[0]*(h[0]/h)**2,':',color='#777777',lw=1,label='Reference slope −2')
    ax[1].set(xlabel='Sample size h (m = h², defects = h)',ylabel='ℓ¹ error',title='Exact finite counts, λ = 1')
    ax[1].legend(frameon=False,fontsize=8)
    dest=ROOT/'figures'
    dest.mkdir(exist_ok=True)
    fig.savefig(dest/'prime_product_transition.pdf')
    fig.savefig(dest/'prime_product_transition.png',dpi=180)
    plt.close(fig)

def main():
    results=dict(exact_verification=exact_checks(),illustrations=convergence_data())
    (ROOT/'data').mkdir(exist_ok=True)
    (ROOT/'data'/'prime_product_verification.json').write_text(json.dumps(results,indent=2)+'\n')
    figures(results['illustrations'])
    print(json.dumps(results['exact_verification'],indent=2))
    print('Wrote exact convergence data and prime_product_transition figures.')

if __name__=='__main__': main()
