"""Second symbolic derivation of the ENTIRE connected-Wick Laurent polynomials.

Use formal independent Gaussians A_i,B_j of variance 1 and C of variance -1/n.
The linear forms (A_i+B_j+C)/sqrt(2n) have exactly the target covariance.
A negative variance is used only as an algebraic Wick functional, not as a
probability measure. Power-sum moments are expanded by equality partitions
and falling factorials; cumulants are then obtained from moment partitions.
This contains no Wick multigraph generation, connected-graph filtering,
edge-color expansion, orbit reduction, or numeric interpolation.

Resource guards: at most 6 vertices and total degree 18; at most 200000 power-
sum monomials in a product. Python's integer display guard is retained at a 640-digit cap.
"""
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import factorial
from common import degree_specification, integer, require

MAX_MONOMIALS=200000


def df(k):
    out=1
    for j in range(1,k+1,2):out*=j
    return out


def set_partitions(r):
    return _set_partitions(integer(r,0,6,"set partition size"))


@lru_cache(None)
def _set_partitions(r):
    integer(r,0,6,"set partition size")
    if r==0:return ((),)
    ans=[]
    for p in set_partitions(r-1):
        ans.append(p+((r-1,),))
        for j in range(len(p)):
            ans.append(p[:j]+(p[j]+(r-1,),)+p[j+1:])
    return tuple(ans)


def pmul(a,b):
    out=defaultdict(int)
    for i,c in a.items():
        for j,d in b.items():out[i+j]+=c*d
    return {i:c for i,c in out.items() if c}


def falling(k):
    return _falling(integer(k,0,6,"falling factorial degree"))


@lru_cache(None)
def _falling(k):
    integer(k,0,6,"falling factorial degree")
    out={0:1}
    for j in range(k):out=pmul(out,{1:1,0:-j})
    return out


@lru_cache(None)
def power_sum_moment(exponents):
    # For q power sums, equality classes of their selected indices are a set
    # partition. Distinct assignments to k classes are (n)_k, exactly.
    out=defaultdict(int)
    for p in set_partitions(len(exponents)):
        c=1
        for block in p:
            degree=sum(exponents[i] for i in block)
            if degree%2:c=0;break
            c*=df(degree-1)
        if not c:continue
        for k,value in falling(len(p)).items():out[k]+=c*value
    return dict(out)


def sum_cell_power(d):
    return _sum_cell_power(integer(d,3,8,"cell degree"))


@lru_cache(None)
def _sum_cell_power(d):
    integer(d,3,8,"cell degree")
    out={}
    for a in range(d+1):
        for b in range(d-a+1):
            c=d-a-b
            key=((a,) if a else (), (b,) if b else (),c,(a==0)+(b==0))
            out[key]=factorial(d)//(factorial(a)*factorial(b)*factorial(c))
    return out


def cell_product(ds):
    return _cell_product(degree_specification(ds,even=False,allow_empty=True))


@lru_cache(None)
def _cell_product(ds):
    ds=degree_specification(ds,even=False,allow_empty=True)
    if not ds:return {((),(),0,0):1}
    out=defaultdict(int)
    for (aa,bb,c,p),value in cell_product(ds[:-1]).items():
        for (ee,ff,g,q),w in sum_cell_power(ds[-1]).items():
            out[tuple(sorted(aa+ee)),tuple(sorted(bb+ff)),c+g,p+q]+=value*w
            if len(out)>MAX_MONOMIALS:raise RuntimeError("power-sum monomial cutoff")
    if len(out)>MAX_MONOMIALS:raise RuntimeError('power-sum monomial cutoff')
    return dict(out)


def moment(ds):
    return _moment(degree_specification(ds,even=False,allow_empty=True))


@lru_cache(None)
def _moment(ds):
    ds=degree_specification(ds,even=False,allow_empty=True)
    total=sum(ds)
    if total%2:return {}
    E=total//2
    out=defaultdict(F)
    for (aa,bb,c,p),value in cell_product(ds).items():
        if c%2:continue
        row=power_sum_moment(aa); col=power_sum_moment(bb)
        if not row or not col:continue
        weight=F(value*df(c-1)*(-1)**(c//2),2**E)
        shift=p-c//2-E
        for k,w in pmul(row,col).items():out[k+shift]+=weight*w
    return {k:v for k,v in out.items() if v}


def cumulant(ds):
    return _cumulant(degree_specification(ds))


@lru_cache(None)
def _cumulant(ds):
    ds=degree_specification(ds)
    out=defaultdict(F)
    for p in set_partitions(len(ds)):
        q={0:1}
        for block in p:
            q=pmul(q,moment(tuple(sorted(ds[i] for i in block))))
            if not q:break
        sign=(-1)**(len(p)-1)*factorial(len(p)-1)
        for k,v in q.items():out[k]+=sign*v
    return {k:v for k,v in out.items() if v}


