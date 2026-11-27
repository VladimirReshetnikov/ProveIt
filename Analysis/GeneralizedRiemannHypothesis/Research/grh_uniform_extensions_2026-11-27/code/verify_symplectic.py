#!/usr/bin/env python3
"""Exact rational checks for uniform symplectic compression theorems.

Standard library only. Finite-field enumerations include GF(4), not Z/4Z.
This is an independent finite check, not a formal proof of asymptotic claims.
Run from the packet directory: python3 code/verify_symplectic.py
"""
from collections import Counter
from decimal import Decimal, localcontext
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from pathlib import Path
import csv
import json
import math
import time

ROOT = Path(__file__).resolve().parents[1]


@lru_cache(None)
def gamma(q, n):
    assert n >= 0
    return math.prod((1 - F(1, q**i) for i in range(1, n+1)), start=F(1))


@lru_cache(None)
def eta(q, n):
    return math.prod((1 - F(1, q**(2*i)) for i in range(1, n+1)), start=F(1))


@lru_cache(None)
def theta(q, n):
    return math.prod((1 - F(1, q**(2*i-1)) for i in range(1, n+1)), start=F(1))


def qp(q, n):
    return F(q**n) if n >= 0 else F(1, q**(-n))


@lru_cache(None)
def gb(q, n, j):
    if j < 0 or j > n:
        return 0
    r = F(1)
    for i in range(j):
        r *= F(q**(n-i)-1, q**(j-i)-1)
    assert r.denominator == 1
    return r.numerator


@lru_cache(None)
def emb(q, D, j, s):
    """Isometric injections of fixed j-space of restricted rank 2s."""
    if not (0 <= 2*s <= j and D % 2 == 0 and j-s <= D//2):
        return 0
    r = qp(q, D*j-j*(j-1)//2)
    for i in range(D//2-j+s+1, D//2+1):
        r *= 1-F(1,q**(2*i))
    assert r.denominator == 1
    return r.numerator


@lru_cache(None)
def types(q, D, j, s):
    t = j-2*s
    if t < 0:
        return 0
    automorphisms = q**(s*(2*s+1))*eta(q,s)*q**(t*t)*gamma(q,t)*q**(2*s*t)
    r = F(emb(q,D,j,s),1)/automorphisms
    assert r.denominator == 1
    return r.numerator


def invert(q, moments):
    n = len(moments)-1
    p = [F(0) for _ in range(n+1)]
    for k in range(n,-1,-1):
        p[k] = moments[k]-sum(gb(q,z,k)*p[z] for z in range(k+1,n+1))
    return p


@lru_cache(None)
def uniform_nullity(q,a,b):
    assert a >= b >= 0
    d = a-b
    p = tuple(qp(q,-k*(k+d))*gamma(q,a)*gamma(q,b)
              /(gamma(q,b-k)*gamma(q,k)*gamma(q,d+k)) for k in range(b+1))
    assert sum(p) == 1 and min(p) >= 0
    return p


@lru_cache(None)
def laws(q,a,b,joint=False):
    assert a >= b >= 2 and a % 2 == b % 2 == 0
    mu, nu, nu0 = [], [], []
    jointmom = []
    for j in range(b+1):
        mu.append(sum(F(types(q,b,j,s)*emb(q,b,j,s),emb(q,a+b,j,s))
                      for s in range(j//2+1)))
        weights = [qp(q,-(a+b)*j+j*j)*types(q,b,j,s)*emb(q,a,j,s)
                   for s in range(j//2+1)]
        nu.append(sum(weights))
        nu0.append(gb(q,b,j)*qp(q,-b*j+j*(j+1)//2))
        if joint:
            row = [F(0) for _ in range(b+1)]
            for s,w in enumerate(weights):
                if not w:
                    continue
                aa,bb = a-2*j+2*s,b-2*j+2*s
                for k,v in enumerate(uniform_nullity(q,aa,bb)):
                    row[k] += w*v
            jointmom.append(row)
    pA, pD, pT = [tuple(invert(q,x)) for x in (mu,nu,nu0)]
    pU = uniform_nullity(q,a,b)
    for p in (pA,pD,pT):
        assert sum(p)==1 and min(p)>=0
    assert all(pD[k]==pT[k]==0 for k in range(1,b+1,2))
    alpha = eta(q,a//2)*eta(q,b//2)/eta(q,(a+b)//2)
    tv_rank = sum(abs(x-y) for x,y in zip(pA,pU))/2
    tv_full = (1-alpha)*pD[0]
    out = dict(pA=pA,pU=pU,pD=pD,pT=pT,alpha=alpha,rank_tv=tv_rank,full_tv=tv_full)
    if joint:
        jointlaw = tuple(tuple(invert(q,[jointmom[j][k] for j in range(b+1)]))
                         for k in range(b+1))
        assert all(x>=0 for row in jointlaw for x in row)
        assert all(sum(row)==pU[k] for k,row in enumerate(jointlaw))
        assert all(sum(jointlaw[k][z] for k in range(b+1))==pD[z] for z in range(b+1))
        out['joint'] = jointlaw
        out['joint_tv'] = sum(abs(jointlaw[k][z]-pU[k]*pD[z])
                              for k in range(b+1) for z in range(b+1))/2
    return out


class Field:
    def __init__(self,q):
        assert q in (2,3,4,5,7)
        self.q=q
    def add(self,x,y):
        return x^y if self.q==4 else (x+y)%self.q
    def neg(self,x):
        return x if self.q==4 else -x%self.q
    def mul(self,x,y):
        if self.q!=4:
            return x*y%self.q
        r=0
        while y:
            if y&1:
                r ^= x
            y >>= 1
            x <<= 1
            if x&4:
                x ^= 7  # x^2+x+1
        return r
    def inv(self,x):
        assert x
        if self.q==4:
            return self.mul(x,x)
        return pow(x,self.q-2,self.q)


def rank(f,rows):
    A=[list(row) for row in rows]
    nr,nc=len(A),len(A[0])
    r=0
    for c in range(nc):
        pivot=next((i for i in range(r,nr) if A[i][c]),None)
        if pivot is None:
            continue
        A[r],A[pivot]=A[pivot],A[r]
        v=f.inv(A[r][c])
        A[r]=[f.mul(v,x) for x in A[r]]
        for i in range(r+1,nr):
            t=A[i][c]
            if t:
                A[i]=[f.add(x,f.neg(f.mul(t,y))) for x,y in zip(A[i],A[r])]
        r+=1
        if r==nr:
            break
    return r


def gram(f,rows):
    nr,nc=len(rows),len(rows[0])
    return tuple(sumfield(f,[f.add(f.mul(rows[r][i],rows[r+1][j]),
                                   f.neg(f.mul(rows[r+1][i],rows[r][j])))
                             for r in range(0,nr,2)])
                 for i in range(nc) for j in range(i+1,nc))


def sumfield(f,seq):
    r=0
    for x in seq:
        r=f.add(r,x)
    return r


def defect(f,g,b):
    return tuple(f.add(int(j==i+1 and i%2==0),f.neg(g[k]))
                 for k,(i,j) in enumerate((i,j) for i in range(b) for j in range(i+1,b)))


def altrows(f,g,b):
    A=[[0]*b for _ in range(b)]
    for x,(i,j) in zip(g,((i,j) for i in range(b) for j in range(i+1,b))):
        A[i][j]=x
        A[j][i]=f.neg(x)
    return A


def enumerate_case(q,a,b):
    """Direct Gram-fibre counts; no embedding or moment formula used."""
    f=Field(q)
    gramB=Counter()
    for flat in product(range(q),repeat=b*b):
        rows=[flat[r*b:(r+1)*b] for r in range(b)]
        gramB[gram(f,rows)] += 1
    unif=Counter()
    weighted=Counter()
    joints=Counter()
    outputs=[]
    total=0
    for flat in product(range(q),repeat=a*b):
        rows=[flat[r*b:(r+1)*b] for r in range(a)]
        k=b-rank(f,rows)
        S=defect(f,gram(f,rows),b)
        z=b-rank(f,altrows(f,S,b))
        c=gramB[S]
        unif[k]+=1
        weighted[k]+=c
        joints[k,z]+=1
        outputs.append(c)
        total+=c
    exact=laws(q,a,b,True)
    assert total==emb(q,a+b,b,b//2)
    assert tuple(F(weighted[k],total) for k in range(b+1))==exact['pA']
    assert tuple(F(unif[k],q**(a*b)) for k in range(b+1))==exact['pU']
    for k in range(b+1):
        for z in range(b+1):
            assert F(joints[k,z],q**(a*b))==exact['joint'][k][z]
    tv=sum(abs(F(c,total)-F(1,q**(a*b))) for c in outputs)/2
    assert tv==exact['full_tv']
    return dict(q=q,a=a,b=b,matrices_enumerated=q**(a*b)+q**(b*b),
                completions=total,full_tv=str(tv),rank_tv=str(exact['rank_tv']),
                joint_tv=str(exact['joint_tv']),passed=True)


def dec(x):
    return Decimal(x.numerator)/Decimal(x.denominator)


def asymptotic_errors(q,a,b,exact):
    # Products truncated at 160 have error < 2^-319, far below displayed precision.
    gi,ei,ti=dec(gamma(q,160)),dec(eta(q,160)),dec(theta(q,160))
    Q=Decimal(q); d=a-b; tau=Q**(-b); sig=Q**(-a)
    cutoff=b+25
    pi=[gi*Q**(-k*(k+d))/(dec(gamma(q,k))*dec(gamma(q,k+d))) for k in range(cutoff+1)]
    xi=[(1+Q**(-d)-Q**k)*v/(Q-1) for k,v in enumerate(pi)]
    lam=[ti*Q**(-(k*(k-1)//2))/dec(gamma(q,k)) if k%2==0 else Decimal(0)
         for k in range(cutoff+1)]
    zeta=[(Q+1-Q**k)*v/(Q*Q-1) for k,v in enumerate(lam)]
    def get(p,k):
        return dec(p[k]) if k<len(p) else Decimal(0)
    rank_res=sum(abs(get(exact['pA'],k)-get(exact['pU'],k)-tau*xi[k]) for k in range(cutoff+1))
    defect_res=sum(abs(get(exact['pD'],k)-get(exact['pT'],k)-sig*zeta[k]) for k in range(cutoff+1))
    C=ti*(Q-(Q+1)*ei)/(Q*Q-1)
    baseline=dec((1-eta(q,b//2))*theta(q,b//2))
    out=dict(q=q,a=a,b=b,gap=d,rank_tv=str(dec(exact['rank_tv'])),
             full_tv=str(dec(exact['full_tv'])),limit=str(ti*(1-ei)),
             predicted_rank_tv=str(gi*sig/((Q-1)*dec(gamma(q,d)))),
             scaled_rank_l1_error=str(rank_res/(sig*tau)),
             scaled_defect_l1_error=str(defect_res/(sig*tau)),
             scaled_full_baseline_error=str(abs(dec(exact['full_tv'])-baseline-C*sig)/(sig*tau)))
    if 'joint' in exact:
        jr=Decimal(0)
        for k in range(cutoff+1):
            for z in range(cutoff+1):
                J=dec(exact['joint'][k][z]) if k<=b and z<=b else Decimal(0)
                covariance=J-get(exact['pU'],k)*get(exact['pD'],z)
                jr+=abs(covariance+tau*(Q*Q-1)*xi[k]*zeta[z])
        out['joint_tv']=str(dec(exact['joint_tv']))
        out['predicted_joint_tv']=str(2*Q*ti*gi*sig/((Q-1)*dec(gamma(q,d))))
        out['scaled_joint_l1_error']=str(jr/(sig*tau))
    return out


def main():
    start=time.time()
    (ROOT/'data').mkdir(exist_ok=True)
    enumeration=[]
    for case in [(2,2,2),(2,4,2),(2,6,2),(2,4,4),(3,2,2),(3,4,2),(4,2,2),(4,4,2),(5,2,2)]:
        r=enumerate_case(*case)
        enumeration.append(r)
        print('Exact enumeration passed:',case,flush=True)
    rows=[]
    with localcontext() as ctx:
        ctx.prec=150
        for q in [2,3,4,5,7]:
            for b in range(2,25,2):
                for a in sorted({b,b+2,b+4,2*b,3*b+2}):
                    joint=(b<=12 and q in (2,3,4))
                    exact=laws(q,a,b,joint)
                    # Independent rank-count formula matches Gaussian moment inversion.
                    check=invert(q,[gb(q,b,j)*qp(q,-a*j) for j in range(b+1)])
                    assert tuple(check)==exact['pU']
                    rows.append(asymptotic_errors(q,a,b,exact))
    fields=list(dict.fromkeys(k for row in rows for k in row))
    with (ROOT/'data'/'symplectic_checks.csv').open('w',newline='') as fp:
        w=csv.DictWriter(fp,fieldnames=fields);w.writeheader();w.writerows(rows)
    maxima={key:max(float(row.get(key,0)) for row in rows)
            for key in fields if key.startswith('scaled_')}
    summary=dict(status='all exact checks passed',parameter_cases=len(rows),
                 joint_cases=sum('joint_tv' in row for row in rows),
                 enumerations=enumeration,
                 total_matrices_enumerated=sum(r['matrices_enumerated'] for r in enumeration),
                 empirical_max_scaled_errors=maxima,
                 warning='Finite checks support but do not prove uniform asymptotic bounds.',
                 decimal_precision=150,infinite_product_factors=160,elapsed_seconds=round(time.time()-start,2))
    (ROOT/'data'/'symplectic_verification.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))


if __name__=='__main__':
    main()
