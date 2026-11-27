#!/usr/bin/env python3
"""Exact rational finite lower/upper certificates for the paper (j=2,3).
Only selecting bracket locations uses floats; all certificates are checked exactly.
Python 3.9+, standard library only. No LP solver, no external data.
"""
from fractions import Fraction as F
from math import isqrt, sqrt, floor, comb, lcm
import argparse


def pmul(p, q):
    a = [0]*(len(p)+len(q)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(q): a[i+j] += x*y
    return a


def moments(k):
    return [1,0,k,0,3*k*k-2*k]


def weights(k, nodes):
    result=[]
    for i,s in enumerate(nodes):
        p=[1]; den=1
        for t in nodes[:i]+nodes[i+1:]:
            p=pmul(p,[-t,1]); den*=s-t
        result.append(F(sum(a*b for a,b in zip(p,moments(k))),den))
    for d in range(len(nodes)):
        assert sum(w*s**d for w,s in zip(result,nodes))==moments(k)[d]
    return result


def nodes_for(k,j,s):
    if j==2:
        inner=[-k/s]
    elif j==3:
        c=(s**3-3*k*s)/(s*s-k)
        b=s-c; a=s*s-c*s-3*k
        disc=sqrt(b*b-4*a)
        inner=[(-b-disc)/2,(-b+disc)/2]
    else: raise ValueError('only j=2,3')
    # Grid of spacing 4 in this parity class. Bracket each interior node
    # with margin >=4; exact validity of weights is checked separately.
    grid=[]
    for t in inner:
        low=s+4*floor((t-s)/4)-4
        grid.extend([low,low+12])
    grid.append(s)
    assert len(set(grid))==len(grid)
    assert all(-k<=t<=s and (t-s)%4==0 for t in grid)
    return grid


def sym_walsh(k,p):
    # Per-character coefficient for a polynomial in S=sum(u_i), by degree.
    c={}; power={0:1}
    for a in p:
        for d,v in power.items(): c[d]=c.get(d,0)+a*v
        nxt={}
        for d,v in power.items():
            if d<k: nxt[d+1]=nxt.get(d+1,0)+(d+1)*v
            if d>0: nxt[d-1]=nxt.get(d-1,0)+(k-d+1)*v
        power=nxt
    return c


def lower(k,j,s):
    # Integer witness (S-s+1-eta)*Q_s(S)^2, with integer approximations
    # of the Hermite interior roots. Sign on the entire cap is exact.
    hfloor=isqrt(k if j==2 else 3*k)
    Q=[hfloor,1] if j==2 else [0,hfloor,1]
    qq=pmul(Q,Q)
    p=pmul([1-s,1],qq)
    c=sym_walsh(k,p)
    parity=(-1)**((k-s)//2)
    for d,v in sym_walsh(k,qq).items():
        c[k-d]=c.get(k-d,0)-parity*v
    mean=c.get(0,0)
    norm=sum(comb(k,d)*abs(v) for d,v in c.items() if d)
    assert mean>0 and norm>0
    return F(mean,norm)


def upper(k,j,s):
    layers=[]
    for t in [s,s-2]:
        ns=nodes_for(k,j,t); ws=weights(k,ns)
        assert all(w>=0 for w in ws), (k,j,t,ns,ws)
        layers.extend((x,w/2) for x,w in zip(ns,ws))
    assert sum(w for x,w in layers)==1
    den=lcm(*(w.denominator for x,w in layers))
    ws=[int(w*den) for x,w in layers]
    ss=[x for x,w in layers]
    signs=[(-1)**((k-x)//2) for x in ss]
    # K_l(s)=[z^l](1-z)^w(1+z)^(k-w). Reflection handles l>k/2.
    prev=[0]*len(ss); curr=[1]*len(ss)
    C=1; best_n=0; best_d=1; best_l=0
    for l in range(k//2+1):
        if l>0:
            v=abs(sum(a*b for a,b in zip(ws,curr)))
            if v*best_d>best_n*C: best_n,best_d,best_l=v,C,l
        if k-l!=l:
            v=abs(sum(a*b*c for a,b,c in zip(ws,curr,signs)))
            if v*best_d>best_n*C: best_n,best_d,best_l=v,C,k-l
        if l==k//2: break
        numer=[s*x-(k-l+1)*y for s,x,y in zip(ss,curr,prev)]
        assert all(a%(l+1)==0 for a in numer)
        prev,curr=curr,[a//(l+1) for a in numer]
        C=C*(k-l)//(l+1)
    return F(best_n,best_d*den),best_l


def run(k,j):
    hscaled=sqrt(k if j==2 else 3*k)
    s=isqrt(k if j==2 else 3*k)
    s-=(s-k)%2
    lo=lower(k,j,s); hi,level=upper(k,j,s)
    assert lo<=hi
    pred=(2 if j==2 else 6)*(1+hscaled-s)
    print(f'{j:1d} {k:6d} {s:4d} {pred:12.6f} {float(lo*k**j):12.6f} {float(hi*k**j):12.6f} {level:6d}')

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--k',type=int,nargs='+',default=[512,1022,1024,4094,4096,8192,16382,16384])
    args=parser.parse_args()
    print('Exact rational certificate checks (decimal display only).')
    print('j      k    s    prediction   scaled lower scaled upper  max degree')
    for j in [2,3]:
        for k in args.k: run(k,j)
    print('PASS: all checked weights, moments, recurrence divisions, and bounds.')
