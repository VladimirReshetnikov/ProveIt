#!/usr/bin/env python3
"""Exact last-gap quadratic and orthant minimum from endpoint-set DP."""
from itertools import combinations
from fractions import Fraction as F
from random import Random
from pathlib import Path
import json

def supports(cols):
    states={0}
    for col in cols:
        new=set()
        for I in states:
            avail=col&~I
            while avail:
                bit=avail&-avail;avail-=bit;new.add(I|bit)
        states=new
    return len(states)
def determinant(A):
    if not A:return F(1)
    if len(A)==1:return A[0][0]
    return sum((-1)**j*A[0][j]*determinant([row[:j]+row[j+1:] for row in A[1:]]) for j in range(len(A)))
def solve(A,b):
    n=len(b);a=[[F(v) for v in row]+[F(y)] for row,y in zip(A,b)]
    for j in range(n):
        k=next((i for i in range(j,n) if a[i][j]),None)
        if k is None:raise RuntimeError("Singular active matrix")
        a[j],a[k]=a[k],a[j]
        d=a[j][j];a[j]=[v/d for v in a[j]]
        for i in range(n):
            if i!=j:
                d=a[i][j];a[i]=[x-d*y for x,y in zip(a[i],a[j])]
    return [row[-1] for row in a]
def data(core,left,right,activities):
    rows=core+left
    bcols=[sum(1<<i for i,row in enumerate(rows) if row>>j&1) for j in range(3)]
    profiles={}
    for mask in range(8):
        start=[bcols[i] for i in range(3) if mask>>i&1]
        c=[]
        for k in range(4):
            total=0
            for I in combinations(range(len(right)),k):
                wt=1
                for i in I:wt*=activities[i]
                total+=wt*supports(start+[right[i] for i in I])
            c.append(total)
        profiles[mask]=c
    lcols=[sum(1<<i for i,row in enumerate(left) if row>>j&1) for j in range(3)]
    q=supports(lcols)
    p=[supports([lcols[j] for j in range(3) if j!=i]) for i in range(3)]
    n=[x.bit_count() for x in lcols]
    T=profiles[0][3]
    if not q or not T:raise RuntimeError("Not genuine")
    C=profiles[7];E=[profiles[7^(1<<i)][2] for i in range(3)]
    if C[3]!=q*T:raise RuntimeError("Top coefficient")
    for i in range(3):
        if profiles[7^(1<<i)][3]!=p[i]*T:raise RuntimeError("Two B coefficient")
        if profiles[1<<i][3]!=n[i]*T:raise RuntimeError("One B coefficient")
    Q=[[5*p[i]*p[j]-(6*q*n[3-i-j] if i!=j else 0) for j in range(3)] for i in range(3)]
    if any(determinant([row[:k] for row in Q[:k]])<=0 for k in range(1,4)):
        raise RuntimeError("Positive definiteness")
    H=[[F(p[i]*p[j])-F(3*q*n[3-i-j],2) if i!=j else F(p[i]*p[j]) for j in range(3)] for i in range(3)]
    for k in range(1,4):
        for I in combinations(range(3),k):
            if determinant([[H[i][j] for j in I] for i in I])<0:raise RuntimeError("Left Schur bound")
    A=5*C[2]**2-12*q*T*C[1]
    c=[5*C[2]*p[i]-6*q*E[i] for i in range(3)]
    if A<=0:raise RuntimeError("Conditioned strictness")
    candidates=[]
    for mask in range(8):
        I=[i for i in range(3) if mask>>i&1]
        x=[F(0)]*3
        vals=solve([[Q[i][j] for j in I] for i in I],[-c[i] for i in I]) if I else []
        for i,v in zip(I,vals):x[i]=v
        if any(x[i]<=0 for i in I):continue
        if any(c[i]+sum(Q[i][j]*x[j] for j in I)<0 for i in range(3) if i not in I):continue
        val=A+sum(c[i]*x[i] for i in I)
        candidates.append((val,x,mask))
    if len(candidates)!=1:raise RuntimeError(("KKT candidates",candidates))
    # Check the exact quadratic against full endpoint coefficients at three fields.
    for w in ([1,2,3],[9,1,7],[2,11,4]):
        P=[0]*7
        for mask,cc in profiles.items():
            v=1
            for i in range(3):
                if mask>>i&1:v*=w[i]
            h=mask.bit_count()
            for j,coeff in enumerate(cc):P[h+j]+=v*coeff
        W=w[0]*w[1]*w[2];z=[F(T,w[i]) for i in range(3)]
        val=A+2*sum(c[i]*z[i] for i in range(3))+sum(Q[i][j]*z[i]*z[j] for i in range(3) for j in range(3))
        if val*W*W!=5*P[5]**2-12*P[4]*P[6]:raise RuntimeError("Quadratic identity")
    return candidates[0],(q,p,n,C,E,T,A,c,Q)

def main():
    rng=Random(441809);best=None;negative=[];faces={}
    for mask in range(512):
        core=[(mask>>(3*i))&7 for i in range(3)]
        left=[1,2,4]+[rng.randint(1,7) for _ in range(4)]
        right=[1,2,4]+[rng.randint(1,7) for _ in range(3)]
        weights=[rng.randint(1,12) for _ in right]
        (v,x,face),info=data(core,left,right,weights)
        scaled=v/info[6]
        faces[str(face)]=faces.get(str(face),0)+1
        item={"core_mask":mask,"minimum":str(v),"relative_to_constant":str(scaled),"active_face":face,"minimizer":[str(a) for a in x],"left_masks":left,"right_masks":right,"right_activities":weights}
        if best is None or scaled<F(best["relative_to_constant"]):best=item
        if v<0:negative.append(item)
    out={"scope":"exact deterministic diagnostics, not a universal finite-activity proof","core_masks_checked":512,"full_quadratic_identity_checks":1536,"all_positive_definite":True,"negative_minima":negative,"active_faces":faces,"least_relative_minimum":best}
    Path(__file__).with_suffix(".json").write_text(json.dumps(out,indent=2)+"\n")
    print(json.dumps(out,indent=2))
if __name__=="__main__":main()

