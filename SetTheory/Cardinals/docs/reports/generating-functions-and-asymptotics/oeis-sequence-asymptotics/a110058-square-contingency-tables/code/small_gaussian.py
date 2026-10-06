"""Independent moment-to-cumulant checks of every generated Laurent polynomial.

At n=1 use a single scalar Gaussian of variance 1/2. At n=2 use the
three independent Gaussians a,b,w of variance 1/8; the four cells are
+a+b+w,+a-b+w,-a+b+w,-a-b+w. Joint moments are obtained by direct
multivariate polynomial multiplication and separate one-variable integration.
Cumulants use the set-partition definition, with no graph connectedness rule,
color expansion, or graph isomorphism machinery.
"""
from collections import defaultdict
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import factorial
from common import degree_specification, integer, require


def double_factorial_odd(k):
    out=1
    for j in range(1,k+1,2):out*=j
    return out


def scalar_moment(k, variance):
    return 0 if k%2 else F(double_factorial_odd(k-1))*variance**(k//2)


def moment_n1(ds):
    return _moment_n1(degree_specification(ds,even=False,allow_empty=True))


@lru_cache(None)
def _moment_n1(ds):
    ds=degree_specification(ds,even=False,allow_empty=True)
    return scalar_moment(sum(ds), F(1,2))


def cell_sum_n2(d):
    return _cell_sum_n2(integer(d,3,8,"cell degree"))


@lru_cache(None)
def _cell_sum_n2(d):
    # Sign summation kills odd powers of a or b, leaving four identical terms.
    integer(d,3,8,"cell degree")
    out={}
    for a in range(0,d+1,2):
        for b in range(0,d-a+1,2):
            w=d-a-b
            out[a,b,w]=4*factorial(d)//(factorial(a)*factorial(b)*factorial(w))
    return out


def product_poly(ds):
    return _product_poly(degree_specification(ds,even=False,allow_empty=True))


@lru_cache(None)
def _product_poly(ds):
    ds=degree_specification(ds,even=False,allow_empty=True)
    if not ds:return {(0,0,0):1}
    out=defaultdict(int)
    for es,c in product_poly(ds[:-1]).items():
        for fs,d in cell_sum_n2(ds[-1]).items():
            out[tuple(e+f for e,f in zip(es,fs))]+=c*d
    return dict(out)


def moment_n2(ds):
    return _moment_n2(degree_specification(ds,even=False,allow_empty=True))


@lru_cache(None)
def _moment_n2(ds):
    ds=degree_specification(ds,even=False,allow_empty=True)
    out=F(0)
    for es,c in product_poly(ds).items():
        term=F(c)
        for e in es:term*=scalar_moment(e,F(1,8))
        out+=term
    return out


def partitions(items):
    if not items:
        yield ()
        return
    first,*rest=items
    for p in partitions(rest):
        yield ((first,),)+p
        for j,block in enumerate(p):
            yield p[:j]+((first,)+block,)+p[j+1:]


def cumulant_from_moments(ds,moment):
    ds=degree_specification(ds)
    out=F(0)
    for p in partitions(list(range(len(ds)))):
        term=F((-1)**(len(p)-1)*factorial(len(p)-1))
        for block in p:term*=moment(tuple(sorted(ds[j] for j in block)))
        out+=term
    return out


def laurent_evaluate(poly,n):
    integer(n,1,2,"independent Gaussian size")
    return sum(F(v)*F(n)**int(k) for k,v in poly.items())


