"""Independent positive-certificate checker. No producer-module imports.

A checked matching vector is NOT independently an unknot certificate.
Negative query results require the complete search; they have no short dual
certificate in this package.
"""
from fractions import Fraction
from functools import reduce
from math import gcd


def _q(x):
    if isinstance(x,(bool,float)) or not isinstance(x,(int,str,Fraction)):
        raise ValueError('not an exact rational')
    return Fraction(x)


def _rank(rows,n):
    basis={}
    for row in rows:
        a=list(map(Fraction,row))
        if len(a)!=n: raise ValueError('dimension mismatch')
        for j in range(n-1,-1,-1):
            if not a[j]: continue
            if j in basis:
                pivot=basis[j];t=a[j]
                a=[u-t*v for u,v in zip(a,pivot)]
            else:
                t=a[j];basis[j]=[v/t for v in a];break
    return len(basis)


def verify_vector(n,equations,conflicts,objective,coordinates,*,zeros=(),extreme=False):
    """Return False for malformed/incorrect packets, including nonintegral rays."""
    try:
        if type(n) is not int or n<1: return False
        x=tuple(_q(v) for v in coordinates);c=tuple(_q(v) for v in objective)
        if len(x)!=n or len(c)!=n or any(v<0 for v in x) or not any(x): return False
        if any(type(j) is not int or not 0<=j<n or x[j] for j in zeros): return False
        rows=tuple(tuple(_q(v) for v in row) for row in equations)
        if any(len(row)!=n or sum((a*b for a,b in zip(row,x)),Fraction(0)) for row in rows): return False
        for pair in conflicts:
            if len(pair)!=2: return False
            a,b=pair
            if type(a) is not int or type(b) is not int or not 0<=a<n or not 0<=b<n or a==b or (x[a] and x[b]): return False
        if sum((a*b for a,b in zip(c,x)),Fraction(0))<=0: return False
        if extreme:
            if any(v.denominator!=1 for v in x): return False
            if reduce(gcd,(int(v) for v in x),0)!=1: return False
            s=[j for j,v in enumerate(x) if v]
            if len(s)-_rank([[row[j] for j in s] for row in rows],len(s))!=1: return False
        return True
    except (ValueError,TypeError,IndexError,ZeroDivisionError,OverflowError):
        return False


def verify_synchronized(blocks,objectives,packet,*,master=None,zeros=None):
    try:
        if packet.get('status')!='POSITIVE': return False
        y=tuple(_q(v) for v in packet['port'])
        vectors=tuple(tuple(_q(v) for v in x) for x in packet['vectors'])
        if len(vectors)!=len(blocks) or len(objectives)!=len(blocks): return False
        if zeros is None: zeros=[() for _ in blocks]
        if len(zeros)!=len(blocks): return False
        value=Fraction(0)
        for b,c,x,z in zip(blocks,objectives,vectors,zeros):
            if len(x)!=b.n or len(c)!=b.n or len(y)!=len(b.ports) or any(v<0 for v in x): return False
            if any(type(j) is not int or not 0<=j<b.n or x[j] for j in z): return False
            if any(sum((a*v for a,v in zip(row,x)),Fraction(0)) for row in b.equations): return False
            if any(x[a] and x[h] for a,h in b.conflicts): return False
            if any(sum((a*v for a,v in zip(row,x)),Fraction(0))!=yy for row,yy in zip(b.ports,y)): return False
            value+=sum((_q(a)*v for a,v in zip(c,x)),Fraction(0))
        if master is not None:
            if len(master)!=len(y):return False
            value+=sum((_q(a)*v for a,v in zip(master,y)),Fraction(0))
        return value>0 and value==_q(packet['value'])
    except (ValueError,TypeError,IndexError,KeyError,ZeroDivisionError):
        return False
