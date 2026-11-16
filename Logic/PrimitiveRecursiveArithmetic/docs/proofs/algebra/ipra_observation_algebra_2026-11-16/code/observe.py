"""Exact finite observation polynomials over Q (reference, not an iPRA checker)."""
from fractions import Fraction as Q
from itertools import permutations

def add(a,b):
    z=[Q(0)]*max(len(a),len(b))
    for i,v in enumerate(a): z[i]+=v
    for i,v in enumerate(b): z[i]+=v
    return trim(z)

def trim(a):
    a=list(a)
    while len(a)>1 and a[-1]==0: a.pop()
    return a

def mul(a,b):
    z=[Q(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): z[i+j]+=x*y
    return trim(z)

def rem(a,f):
    assert f[-1]==1 and len(f)>=2
    a=trim(a); d=len(f)-1
    while len(a)>d:
        c=a[-1]; i=len(a)-1-d
        for j in range(d+1): a[i+j]-=c*f[j]
        a=trim(a)
    return a+[Q(0)]*(d-len(a))

def matmul(A,B):
    n=len(A)
    return [[sum((A[i][k]*B[k][j] for k in range(n)),Q(0)) for j in range(n)] for i in range(n)]

def matpoly(g,M):
    n=len(M); I=[[Q(int(i==j)) for j in range(n)] for i in range(n)]
    Z=[[Q(0) for _ in range(n)] for _ in range(n)]
    for c in reversed(g):
        Z=matmul(Z,M)
        for i in range(n): Z[i][i]+=c
    return Z

def companion(f):
    d=len(f)-1
    assert d>=1 and f[-1]==1
    M=[[Q(0) for _ in range(d)] for _ in range(d)]
    for j in range(d-1): M[j+1][j]=Q(1)
    for i in range(d): M[i][d-1]=-f[i]
    return M

def sign(p):
    inv=sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))
    return -1 if inv%2 else 1

def obs(f,g):
    M=matpoly(g,companion(f));d=len(M)
    # polynomial coefficients in T from a signed permutation determinant
    out=[Q(0)]
    for p in permutations(range(d)):
        term=[Q(1)]
        for i,j in enumerate(p):
            term=mul(term, [-M[i][j],Q(1)] if i==j else [-M[i][j]])
        if sign(p)==-1: term=[-x for x in term]
        out=add(out,term)
    return trim(out)

def compose(h,g):
    v=[Q(0)]
    for c in reversed(h): v=add(mul(v,g),[c])
    return v

if __name__=='__main__':
    f=[Q(-2),Q(0),Q(1)]
    print('f=',f,'observable(y)=',obs(f,[Q(0),Q(1)]))
    print('observable(y^2)=',obs(f,[Q(0),Q(0),Q(1)]))
