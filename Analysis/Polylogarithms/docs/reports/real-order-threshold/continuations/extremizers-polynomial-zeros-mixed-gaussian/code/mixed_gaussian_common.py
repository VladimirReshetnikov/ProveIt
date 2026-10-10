"""Reusable Euler arithmetic for the mixed Gaussian research certificate.

The finite-integer method is adapted from the incoming file
polylogarithms_uniform_continuation/code/gaussian/verify_gaussian_proximity.py
at ProveIt revision 4c173c06cc32c9cea554b39be1837ad2ae897fc1.
Its analytic error bounds are proved in the accompanying article.
"""
from fractions import Fraction as Q
from math import lcm


class Interval:
    __slots__=('lo','hi')
    def __init__(self,lo,hi=None):
        self.lo=Q(lo)
        self.hi=Q(lo if hi is None else hi)
        if self.lo>self.hi: raise ValueError('Reversed interval')
    def __add__(self,other):
        if not isinstance(other,Interval): other=Interval(other)
        return Interval(self.lo+other.lo,self.hi+other.hi)
    __radd__=__add__
    def __mul__(self,other):
        if not isinstance(other,Interval): other=Interval(other)
        corners=[a*b for a in (self.lo,self.hi) for b in (other.lo,other.hi)]
        return Interval(min(corners),max(corners))
    __rmul__=__mul__
    def __pow__(self,n):
        if n<0 or self.lo<0: raise ValueError('Positive interval power required')
        return Interval(self.lo**n,self.hi**n)
    def record(self):
        return {'lower':[str(self.lo.numerator),str(self.lo.denominator)],
                'upper':[str(self.hi.numerator),str(self.hi.denominator)]}


def integer_euler_weights(N):
    scale=1<<N
    tail=scale-1
    c=1
    weights=[]
    for n in range(N):
        weights.append((-1)**n*tail)
        c=c*(N-n)//(n+1)
        tail-=c
    if tail!=0:
        raise ArithmeticError('Euler weight recurrence did not exhaust the tail')
    return weights,scale


class ExactEuler:
    def __init__(self,N):
        self.N=N
        self.weights,self.scale=integer_euler_weights(N)
        self.D=lcm(*range(1,2*N+1))
    def gaussian(self,a,b):
        if not (a>=2 and b>=1):
            raise ValueError('Gaussian Euler bounds require a >= 2 and b >= 1')
        num=0
        harmonic=0
        for n,w in enumerate(self.weights):
            if n:
                harmonic+=(self.D//(2*n-1))**b+(self.D//(2*n))**b
            num+=w*harmonic*(self.D//(2*n+1))**a
        E=Q(num,self.scale*self.D**(a+b))
        bound=Q(self.N+1,self.scale*3**a)*(1+Q(1,2**b))
        return Interval(E-bound,E)
    def mixed(self,p):
        if not p>=2:
            raise ValueError('Mixed Euler bounds require p >= 2')
        num=0
        harmonic=0
        for n,w in enumerate(self.weights):
            if n: harmonic+=self.D//n
            num+=w*harmonic*(self.D//(2*n+1))**p
        E=Q(num,self.scale*self.D**(p+1))
        return Interval(E-Q(self.N+1,self.scale*3**p),E)
    def single(self,s,odd):
        if not s>=1:
            raise ValueError('Single Euler bounds require s >= 1')
        num=sum(w*(self.D//(2*n+1 if odd else n+1))**s
                for n,w in enumerate(self.weights))
        E=Q(num,self.scale*self.D**s)
        return Interval(E,E+Q(1,self.scale))
    def beta(self,s): return self.single(s,True)
    def zeta(self,s):
        if not s>1:
            raise ValueError('Zeta Euler bounds require s > 1')
        return self.single(s,False)*Q(2**(s-1),2**(s-1)-1)


def arctangent_inverse(q,N):
    E=sum((Q((-1)**n,(2*n+1)*q**(2*n+1)) for n in range(N)),Q())
    error=Q(1,(2*N+1)*q**(2*N+1))
    return Interval(E-error,E) if N%2 else Interval(E,E+error)


def elementary_intervals(arctangent_terms=650,logarithm_terms=950):
    pi=16*arctangent_inverse(5,arctangent_terms)
    pi+=(-4)*arctangent_inverse(239,arctangent_terms)
    M=logarithm_terms
    E=sum((Q(2,(2*n+1)*3**(2*n+1)) for n in range(M)),Q())
    log2=Interval(E,E+Q(9,4*(2*M+1)*3**(2*M+1)))
    return pi,log2


def numerical_euler_values(p,N,digits):
    """Discovery only. Imports mpmath lazily; exact replay does not need it."""
    import mpmath as mp
    mp.mp.dps=digits
    pairs=[(a,p+1-a) for a in range(p,1,-2)]
    values=[mp.mpf(0)]*(len(pairs)+1)
    hn=mp.mpf(0)
    hs={b:mp.mpf(0) for a,b in pairs}
    weights,scale=integer_euler_weights(N)
    for n,weight in enumerate(weights):
        if n:
            hn+=mp.mpf(1)/n
            for b in hs:
                hs[b]+=mp.mpf(1)/(2*n-1)**b+mp.mpf(1)/(2*n)**b
        w=mp.mpf(weight)/scale
        values[0]+=w*hn/(2*n+1)**p
        for j,(a,b) in enumerate(pairs,1):
            values[j]+=w*hs[b]/(2*n+1)**a
    beta=lambda s:(mp.zeta(s,mp.mpf(1)/4)-mp.zeta(s,mp.mpf(3)/4))/mp.mpf(4)**s
    names=[f'S{p}']+[f'g{a},{b}' for a,b in pairs]+[f'pi^{p+1}']
    names += [f'beta({2*j})*zeta({p+1-2*j})' for j in range(1,p//2)]
    names += [f'beta({p})*log(2)']
    values += [mp.pi**(p+1)]
    values += [beta(2*j)*mp.zeta(p+1-2*j) for j in range(1,p//2)]
    values += [beta(p)*mp.log(2)]
    return names,values
