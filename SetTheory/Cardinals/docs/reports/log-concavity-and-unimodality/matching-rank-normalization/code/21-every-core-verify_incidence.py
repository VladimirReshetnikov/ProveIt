#!/usr/bin/env python3
"""Exact integer-vector checks; supplementary to the proof, no numeric tolerances."""
import itertools as it, json, random
from collections import Counter
from pathlib import Path

def det(rows):
    n=len(rows)
    if n==0:return 1
    a=[list(x) for x in rows]
    sg=1; prev=1
    for k in range(n-1):
        if not a[k][k]:
            h=next((j for j in range(k+1,n) if a[j][k]),None)
            if h is None:return 0
            a[k],a[h]=a[h],a[k];sg=-sg
        pivot=a[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                num=a[i][j]*pivot-a[i][k]*a[k][j]
                if num%prev:raise RuntimeError("Bareiss division failed")
                a[i][j]=num//prev
            a[i][k]=0
        prev=pivot
    return sg*a[-1][-1]

def cross(x,y):return (x[1]*y[2]-x[2]*y[1],x[2]*y[0]-x[0]*y[2],x[0]*y[1]-x[1]*y[0])
def dot(x,y):return sum(a*b for a,b in zip(x,y))
def canonical(v):
    from math import gcd
    d=0
    for x in v:d=gcd(d,x)
    if not d:return None
    w=tuple(x//d for x in v)
    return tuple(-x for x in w) if next(x for x in w if x)<0 else w
def matvec(C,v):return tuple(dot(row,v) for row in C)
def rank3(L):return any(det(z) for z in it.combinations(L,3))
def require(x,msg):
    if not x:raise RuntimeError(msg)
E=[(1,0,0),(0,1,0),(0,0,1)]

def plane_check(L,a,weights=None):
    if weights is None:weights=[1]*len(L)
    beta=sum(w for l,w in zip(L,weights) if dot(l,a)!=0)
    q=sum(weights[i]*weights[j]*weights[k] for i,j,k in it.combinations(range(len(L)),3) if det([L[i],L[j],L[k]]))
    if not beta:return None
    hist=Counter()
    for i,j in it.combinations(range(len(L)),2):
        x,y=L[i],L[j]
        v=cross(x,y)
        if not any(v):continue
        delta=cross(a,v)
        if any(delta):hist[canonical(delta)]+=weights[i]*weights[j]
    h=sum(hist.values());Q=h*h-sum(x*x for x in hist.values())
    require(2*Q>=3*q*beta,"plane incidence failed")
    return Q,beta

def matrix_check(L,C,R,weights,full=False):
    q=sum(det(z)!=0 for z in it.combinations(L,3))
    P=[cross(x,y) for x,y in it.combinations(L,2) if any(cross(x,y))]
    W=[matvec(C,v) for v in P]
    U=sum(w*sum(det([r,*z])!=0 for z in it.combinations(E,2)) for r,w in zip(R,weights))
    a=sum(weights[i]*weights[j]*sum(det([R[i],R[j],e])!=0 for e in E) for i,j in it.combinations(range(len(R)),2))
    T=sum(weights[i]*weights[j]*weights[k]*(det([R[i],R[j],R[k]])!=0) for i,j,k in it.combinations(range(len(R)),3))
    PV=sum(w*sum(det([r,v,e])!=0 for v in W for e in E) for r,w in zip(R,weights))
    PB=sum(weights[i]*weights[j]*sum(det([R[i],R[j],v])!=0 for v in W) for i,j in it.combinations(range(len(R)),2))
    Q=N=0
    for r,weight in zip(R,weights):
        beta=sum(det([list(C[i])+[r[i]] for i in range(3)]+[list(l)+[0]])!=0 for l in L)
        Qj=2*sum(det([r,x,y])!=0 for x,y in it.combinations(W,2))
        kappa=q*sum(det([r,*z])!=0 for z in it.combinations(E,2))+sum(det([r,v,e])!=0 for v in W for e in E)+beta
        require(2*Qj>=3*q*beta,"mapped incidence failed")
        require(3*kappa>=7*beta,"refined unit count failed")
        Q+=weight*Qj;N+=weight*beta
    c=[None,q*U+PV+N,q*a+PB,q*T]
    require(2*c[2]**2>=6*q*T*(c[1]-N)+3*T*Q,"right Schur failed")
    require(8*c[2]**2>=21*c[1]*c[3],"21/8 inequality failed")
    require(28*c[2]**2>=75*c[1]*c[3],"75/28 inequality failed")
    if full:
        base=[list(C[i])+[r[i] for r in R] for i in range(3)]+[list(l)+[0]*len(R) for l in L]
        coeff=[]
        for k in range(4):
            total=0
            for J in it.combinations(range(len(R)),k):
                cols=[0,1,2]+[3+j for j in J]
                f=1
                for j in J:f*=weights[j]
                for I in it.combinations(range(len(L)+3),k+3):
                    total+=f*(det([[base[i][j] for j in cols] for i in I])!=0)
            coeff.append(total)
        require(coeff[1:]==c[1:],"direct endpoint coefficient mismatch")
        require((len(L)-1)*coeff[1]**2>=2*len(L)*coeff[0]*coeff[2],"ambient lower bound failed")
        return coeff
    return c[1:]

def main():
    rng=random.Random(927431)
    plane_cases=0; weighted_plane_cases=0; full_cases=0; matrix_cases=0
    def sample(n):
        while True:
            v=[tuple(rng.randint(-2,2) for _ in range(3)) for _ in range(n)]
            if all(any(x) for x in v) and rank3(v):return v
    examples=[]
    for z in range(160):
        L=sample(3+z%6)
        for a in E+sample(3):
            plane_check(L,a);plane_cases+=1
            plane_check(L,a,[1+(i+z)%5 for i in range(len(L))]);weighted_plane_cases+=1
    # Every Boolean core mask is represented, including all singular ranks.
    for mask in range(512):
        C=[tuple((1+i*3+j)*((mask>>(3*i+j))&1) for j in range(3)) for i in range(3)]
        L=sample(3+mask%4);R=sample(3+mask%2)
        weights=[1+rng.randrange(5) for _ in R]
        full=mask%16==0 or mask in [7,15,73,84,238,511]
        out=matrix_check(L,C,R,weights,full)
        matrix_cases+=1;full_cases+=int(full)
        if full and len(examples)<5:examples.append({"core_mask":mask,"coefficients":out})
    result={"status":"passed","plane_incidence_cases":plane_cases,"weighted_plane_incidence_cases":weighted_plane_cases,"all_core_matrix_cases":matrix_cases,"direct_full_endpoint_enumerations":full_cases,"examples":examples}
    Path(__file__).with_suffix(".json").write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result,indent=2))
if __name__=="__main__":main()
