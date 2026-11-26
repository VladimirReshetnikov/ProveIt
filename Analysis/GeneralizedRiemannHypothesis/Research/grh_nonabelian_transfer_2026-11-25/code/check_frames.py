#!/usr/bin/env python3
"""Exact certificates for tight frames over the discriminant-229 cubic and S3 fields.
Only Python's standard library is required. This checks identities, not analytic GRH.
"""
from fractions import Fraction
from math import isqrt
from pathlib import Path
import json

def transpose(A): return [list(x) for x in zip(*A)]
def matmul(A,B):
    return [[sum(x*y for x,y in zip(row,col)) for col in zip(*B)] for row in A]
def det(A):
    A=[[Fraction(x) for x in row] for row in A]
    n=len(A); out=Fraction(1)
    for i in range(n):
        j=next((j for j in range(i,n) if A[j][i]),None)
        if j is None:return 0
        if j!=i:A[i],A[j]=A[j],A[i];out=-out
        pivot=A[i][i];out*=pivot
        for j in range(i+1,n):
            q=A[j][i]/pivot
            for k in range(i+1,n):A[j][k]-=q*A[i][k]
    return out

def outer_sum(vs,ms):
    n=len(vs[0])
    return [[sum(m*v[i]*v[j] for v,m in zip(vs,ms)) for j in range(n)] for i in range(n)]
def check(name,G,C,vs,ms):
    n=len(G)
    assert outer_sum(vs,ms)==C
    assert matmul(G,C)==[[229*(i==j) for j in range(n)] for i in range(n)]
    assert transpose(G)==G and transpose(C)==C
    norms=[sum(v[i]*G[i][j]*v[j] for i in range(n) for j in range(n)) for v in vs]
    assert sum(m*a for m,a in zip(ms,norms))==229*n
    assert all(det([row[:k] for row in G[:k]])>0 for k in range(1,n+1))
    assert any(x%229 for row in C for x in row) # denominator of G^-1 is exactly 229
    return {'field':name,'gram':G,'inverse_gram_times_229':C,'vectors':vs,'multiplicities':ms,
            'total_vectors':sum(ms),'norms':norms,'gram_determinant':int(det(G)),
            'optimal_integer_frame_bound':229,'all_identities_exact':True}

assert all(229%d for d in range(2,isqrt(229)+1))
T=[[3,0,8],[0,8,-3],[8,-3,32]]
C3=[[247,-24,-64],[-24,32,9],[-64,9,24]]
v3=[[0,2,1],[1,-1,1],[2,-1,1],[4,-5,-2],[15,0,-4]]
m3=[1,2,1,1,1]
# Newton sums for x^3-4x+1; all ordered pairs of distinct roots yield six embeddings.
p=[3,0,8]
for k in range(3,7):p.append(4*p[k-2]-p[k-3])
mons=[(0,0),(1,0),(2,0),(0,1),(1,1),(2,1)]
G6=[[p[i+k]*p[j+l]-p[i+j+k+l] for k,l in mons] for i,j in mons]
C6=[[125,-16,-32,4,0,-3],[-16,32,3,0,-3,8],[-32,3,16,-3,8,0],
    [4,0,-3,32,-6,-8],[0,-3,8,-6,16,0],[-3,8,0,-8,0,6]]
v6=[[0,2,-2,-2,-1,1],[1,-2,-2,4,-2,-1],[2,2,0,1,2,1],
    [4,1,-1,1,-1,0],[4,1,-1,2,0,-1],[6,-4,-1,-1,2,-1],[6,-1,-2,-2,-1,1]]
m6=[1,1,1,2,1,1,1]
results=[check('real cubic Q(alpha)',T,C3,v3,m3),check('S3 splitting field Q(alpha,beta)',G6,C6,v6,m6)]
assert det(T)==229 and det(G6)==229**3
# (X-29)^2(X+58) = X^3 -4 X +1 mod 229.
assert (-3*29**2+4)%229==0 and (2*29**3-1)%229==0
out={'status':'passed','arithmetic':'exact integer and rational arithmetic','certificates':results,
     'scope':'Frame identities and discriminants; no claim of Lean compilation or new RH proof.'}
path=Path(__file__).resolve().parents[1]/'certificates/frame_certificates.json';path.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':'passed','cubic_bound':229,'cubic_vectors':6,'S3_bound':229,'S3_vectors':8,'certificate':str(path)},indent=2))
