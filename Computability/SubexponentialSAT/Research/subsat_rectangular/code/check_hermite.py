#!/usr/bin/env python3
"""Exact finite checks for the asymmetric Hermite symmetrization lemma."""
from fractions import Fraction as F
from itertools import product
import json

def require(condition):
    if not condition:
        raise AssertionError("Exact Hermite check failed")

def v2(n):
    require(n)
    return (abs(n)&-abs(n)).bit_length()-1

def loss_vector(q):
    N=(len(q)).bit_length()-1
    require(len(q)==1<<N and q[0]==0)
    out=[]
    for t in range(1,1<<N):
        i=v2(t); D=1<<(N-1-i)
        L=sum(q[v]*(v2(t-v)-v2(v)) for v in range(1,1<<N) if v!=t)+(q[t]-1)*(N-i)
        out.append(F(L,D))
    return out

def certificate(q):
    losses=loss_vector(q)
    active=[losses[t-1] for t in range(1,len(q)) if q[t]>0]
    return max([F(0)]+active)

def sym(q):
    N=len(q).bit_length()-1
    r=[F(0)]*len(q)
    for i in range(N):
        ns=[t for t in range(1,len(q)) if v2(t)==i]
        avg=sum(q[t] for t in ns)/F(len(ns))
        for t in ns:r[t]=avg
    return r

def potential_formula(q,t):
    N=len(q).bit_length()-1;i=v2(t)
    return sum(sum(q[x] for x in range(len(q)) if x%(1<<k)==t%(1<<k))-sum(q[x] for x in range(len(q)) if x%(1<<k)==0) for k in range(i+1,N+1))-(N-i)

def exact_relaxed(a,u,W):
    # Finite full top-cardinal loss, including the -1 in q_t-1.
    r=[F(0)]*u;c=[F(0)]*u
    for i in reversed(range(u)):
        D=1<<(a-i);n=a+1-i;diag=F(2)-F(1,D)
        r[i]=(1+sum(F(j,1<<j)*r[i+j] for j in range(1,u-i)))/diag
        c[i]=(F(n,D)+sum(F(j,1<<j)*c[i+j] for j in range(1,u-i)))/diag
    R=sum(F(1,1<<i)*r[i] for i in range(u));C=sum(F(1,1<<i)*c[i] for i in range(u))
    eta=max(F(0),(W-C)/R)
    q=[eta*r[i]+c[i] for i in range(u)]
    if W<C:q=[x*W/C for x in q]
    return eta,q,R,C

def main():
    counts=[]
    for N,cap in [(1,5),(2,4),(3,2)]:
        cnt=0
        for vals in product(range(cap+1),repeat=(1<<N)-1):
            q=[F(0)]+list(map(F,vals));L=loss_vector(q)
            require(certificate(q)==max([F(0)]+L))
            require(certificate(sym(q))<=certificate(q))
            for t in range(1,len(q)):
                require(L[t-1]*(1<<(N-1-v2(t)))==potential_formula(q,t))
            cnt+=1
        counts.append({'N':N,'cap':cap,'vectors':cnt})
    minimax=[]
    for a in range(1,8):
        for u in range(1,a+1):
            for W in [F(1,3),F(1),F(10),F(123)]:
                eta,qi,R,C=exact_relaxed(a,u,W)
                q=[F(0)]*(1<<(a+1))
                for t in range(1,len(q)):
                    i=v2(t)
                    if i<u:q[t]=qi[i]
                require(sum(q)==W*(1<<a))
                require(certificate(q)==eta)
                minimax.append((a,u,str(W),str(eta)))
    result={'exhaustive':counts,'finite_minimax_cases':len(minimax),'checks':'all passed'}
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
