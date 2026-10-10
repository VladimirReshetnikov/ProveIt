#!/usr/bin/env python3
"""Exact O(w^2) normal forms for the odd-weight coefficient row module.

No numerical constants, matrix ranks, or external packages are used here.
The theorem concerns the precise product-only matrix A_w in the manuscript.
Coordinates are (a,b,r,s), with canonical colors and omitted (1,w-1,0,1).
"""
from fractions import Fraction
from functools import lru_cache

COLORS=((0,1),(1,0),(1,1),(1,2),(1,3),(2,1))

def coordinates(w):
    if w<3 or w%2!=1:raise ValueError('odd weight >=3 required')
    return tuple((a,w-a,r,s) for a in range(1,w) for r,s in COLORS
                 if (a,r,s)!=(1,0,1))

@lru_cache(None)
def pascal(w):
    """Precompute the needed binomial coefficients in O(w^2) additions."""
    rows=[(1,)]
    for n in range(1,w):
        prev=rows[-1]
        rows.append((1,)+tuple(prev[k-1]+prev[k] for k in range(1,n))+(1,))
    return tuple(rows)

def entry(table,n,k):
    return table[n][k] if 0<=k<=n else 0

def effective_arrays(w,target):
    """Map a sparse arbitrary target into the two G,D polynomial sectors."""
    allowed=set(coordinates(w))
    if not set(target)<=allowed:raise ValueError('noncanonical target coordinate')
    t={key:Fraction(c) for key,c in target.items()}
    def get(a,r,s):return t.get((a,w-a,r,s),Fraction(0))
    g=[Fraction(0)]*w;d=g.copy();P=pascal(w)
    for c in range(1,w):
        g[c]=get(c,1,0)-get(w-c,0,1)
        d[c]=get(c,1,2)-get(w-c,2,1)
        for a in range(w-c,w):
            f=(-1)**(w-a-1)*P[c-1][w-a-1]
            g[c]+=f*get(a,1,3)
            d[c]-=f*get(a,1,1)
    return g,d

def normal_form(w,target):
    """Return coefficients on the free G_a,D_a coordinates, a>(w-1)/2."""
    m=(w-1)//2;g,d=effective_arrays(w,target);out={};P=pascal(w)
    for sector,v,sgn in [('G',g,1),('D',d,-1)]:
        cs=[Fraction(0)]*(m+1)
        for p in range(1,m+1):
            cs[p]=sum((-1)**(p-a)*P[p-1][a-1]*v[a]
                      for a in range(1,p+1))
        for a in range(m+1,w):
            coeff=v[a]-sum(cs[p]*(entry(P,a-1,p-1)+
                                      sgn*entry(P,a-1,w-p-1))
                           for p in range(1,m+1))
            if coeff:out[(sector,a)]=coeff
    return out

def moments(w,target):
    """Nonzero pairings with the complete explicit integral kernel basis."""
    g,d=effective_arrays(w,target);out={};P=pascal(w)
    for sector,v,parity in [('G',g,1),('D',d,0)]:
        for j in range(parity,w-1,2):
            c=sum((-1)**(j-k)*(1<<k)*P[j][k]*v[w-1-k]
                  for k in range(j+1))
            if c:out[(sector,j)]=c
    return out

def kernel_vector(w,sector,j):
    """Integral witness corresponding to X^(w-2-j)(2Y-X)^j."""
    keys=coordinates(w);n=w-2
    if sector not in ('G','D') or not(0<=j<=n) or j%2!=(sector=='G'):
        raise ValueError('invalid sector or basis exponent')
    h=[0]*w;P=pascal(w)
    for k in range(j+1):h[w-1-k]=(-1)**(j-k)*(1<<k)*P[j][k]
    out={}
    for a,b,r,s in keys:
        c=0
        if sector=='G':
            if (r,s)==(1,0):c=h[a]
            elif (r,s)==(0,1):c=-h[w-a]
            elif (r,s)==(1,3):
                c=(-1)**(b-1)*sum(P[k-1][b-1]*h[k] for k in range(b,w))
        else:
            if (r,s)==(1,2):c=h[a]
            elif (r,s)==(2,1):c=-h[w-a]
            elif (r,s)==(1,1):
                c=-(-1)**(b-1)*sum(P[k-1][b-1]*h[k] for k in range(b,w))
        if c:out[(a,b,r,s)]=c
    return out

def decide(w,target):
    """Return membership; on failure return an exact integral separating witness."""
    ms=moments(w,target)
    if not ms:return {'member':True,'normal_form':{}}
    sector,j=next(iter(ms));v=kernel_vector(w,sector,j)
    pairing=sum(Fraction(c)*v.get(k,0) for k,c in target.items())
    assert pairing==ms[(sector,j)]
    return {'member':False,'normal_form':normal_form(w,target),
            'witness':v,'pairing':pairing,'basis_descriptor':(sector,j)}

if __name__=='__main__':
    target={(4,1,1,0):3,(3,2,1,0):3,(2,3,1,0):9,(4,1,1,2):7}
    ans=decide(5,target)
    print('S4 target rowspace member:',ans['member'])
    print('Formal normal form:',ans['normal_form'])
    print('Witness basis:',ans['basis_descriptor'],'pairing:',ans['pairing'])
