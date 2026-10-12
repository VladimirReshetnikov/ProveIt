"""Small independent exhaustive oracle; no projective_ports imports.

Reverse-column Gaussian elimination, independent of the producer's RREF.
Only used on finite, explicitly bounded audit instances.
"""
from fractions import Fraction as F
from itertools import combinations
from math import gcd,lcm
from functools import reduce


def one_dimensional_kernel(rows,n):
    piv={}
    for row in rows:
        a=list(map(F,row))
        for j in range(n-1,-1,-1):
            if not a[j]:continue
            if j in piv:
                q=a[j];a=[u-q*v for u,v in zip(a,piv[j])]
            else:
                q=a[j];piv[j]=tuple(v/q for v in a);break
    if len(piv)!=n-1:return None
    free=next(j for j in range(n) if j not in piv)
    x=[F(0)]*n;x[free]=F(1)
    for j in sorted(piv):
        x[j]=-sum((piv[j][k]*x[k] for k in range(j)),F(0))
    if not (all(v>0 for v in x) or all(v<0 for v in x)):return None
    if x[0]<0:x=[-v for v in x]
    den=lcm(*(v.denominator for v in x));v=[int(a*den) for a in x]
    g=reduce(gcd,v);return tuple(a//g for a in v)


def all_rays(n,rows,conflicts):
    out=[]
    for k in range(1,n+1):
        for s in combinations(range(n),k):
            support=set(s)
            if any(a in support and b in support for a,b in conflicts):continue
            v=one_dimensional_kernel([[row[j] for j in s] for row in rows],k)
            if v is None:continue
            x=[0]*n
            for j,a in zip(s,v):x[j]=a
            out.append(tuple(x))
    return tuple(out)


def positive(rays,c,zeros=()):
    return next((r for r in rays if not any(r[j] for j in zeros)
                 and sum((F(a)*b for a,b in zip(c,r)),F(0))>0),None)


def cartesian_modes(costs):
    """Exact baseline for the four-ray synchronized sleeve family.

    Enumerate every global binary mode history, then solve its common-interval
    linear objective at both endpoints. No early stopping or approximation.
    """
    from itertools import product
    domains=((F(0),F(2,3)),(F(1,3),F(1)))
    lines=[]
    for c in costs:
        loc=[]
        for lo,hi,a,b in ((F(0),F(2,3),F(c[0],3),F(c[1],3)),
                         (F(1,3),F(1),F(c[2],3),F(c[3],3))):
            slope=(b-a)/(hi-lo); loc.append((a-slope*lo,slope))
        lines.append(loc)
    best=None
    for mode in product(range(2),repeat=len(costs)):
        lo=max(domains[z][0] for z in mode);hi=min(domains[z][1] for z in mode)
        if lo>hi:continue
        a=sum((lines[i][z][0] for i,z in enumerate(mode)),F(0))
        b=sum((lines[i][z][1] for i,z in enumerate(mode)),F(0))
        value=max(a+b*lo,a+b*hi)
        if best is None or value>best:best=value
    return best
