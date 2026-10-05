"""Auditable standard-library Q[n] and Q(n), and sparse polynomial arithmetic.

Every equality is an exact coefficient equality, never a sampled identity.
Guards deliberately use exceptions so that Python -O retains every check.
"""
from fractions import Fraction as F
from functools import reduce
from math import gcd


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def trim(a):
    a = list(a)
    while a and not a[-1]:
        a.pop()
    return tuple(a)


class Poly:
    """Dense univariate polynomial, coefficients in ascending order."""
    def __init__(self, a=0):
        self.c = a.c if isinstance(a, Poly) else trim(a if isinstance(a, (list, tuple)) else [a])
    def __bool__(self): return bool(self.c)
    def __eq__(self, b): return self.c == Poly(b).c
    def __add__(self, b):
        b = Poly(b)
        return Poly([(self.c[i] if i < len(self.c) else 0)+(b.c[i] if i < len(b.c) else 0)
                     for i in range(max(len(self.c), len(b.c)))])
    __radd__ = __add__
    def __neg__(self): return Poly([-a for a in self.c])
    def __sub__(self, b): return self + -Poly(b)
    def __rsub__(self, b): return Poly(b) + -self
    def __mul__(self, b):
        b = Poly(b)
        if not self or not b: return Poly()
        c = [0]*(len(self.c)+len(b.c)-1)
        for i, a in enumerate(self.c):
            for j, v in enumerate(b.c): c[i+j] += a*v
        return Poly(c)
    __rmul__ = __mul__
    def __pow__(self, k):
        require(isinstance(k, int) and k >= 0, 'invalid polynomial power')
        a, b = Poly(1), self
        while k:
            if k & 1: a = a*b
            k //= 2
            if k: b = b*b
        return a
    def degree(self): return len(self.c)-1
    def value(self, x):
        a = 0
        for c in reversed(self.c): a = a*x+c
        return a
    def shift(self, k=1): return self.value(Poly([k, 1]))


def divmod_poly(a, b):
    a, b = Poly(a), Poly(b)
    require(bool(b), 'polynomial division by zero')
    r = list(a.c); q = [F(0)]*max(0, len(r)-len(b.c)+1)
    while r and len(r) >= len(b.c):
        d = len(r)-len(b.c); c = F(r[-1], b.c[-1]); q[d] = c
        for i, v in enumerate(b.c): r[d+i] -= c*v
        while r and not r[-1]: r.pop()
    return Poly(q), Poly(r)


def exact_quotient(a, b):
    q, r = divmod_poly(a, b)
    require(not r, 'inexact polynomial quotient')
    return q


def primitive(a):
    a = Poly(a)
    if not a: return a
    scale = 1
    for c in a.c:
        d = F(c).denominator; scale = scale*d//gcd(scale, d)
    ints = [int(c*scale) for c in a.c]
    common = reduce(gcd, ints)
    if ints[-1] < 0: common = -common
    return Poly([v//common for v in ints])


def polynomial_gcd(a, b):
    a, b = primitive(a), primitive(b)
    while b:
        a, b = b, primitive(divmod_poly(a, b)[1])
    return a


class Rat:
    """Reduced rational function of n, with primitive integer coefficient pair."""
    def __init__(self, a=0, b=1):
        if isinstance(a, Rat):
            require(Poly(b) == 1, 'nested rational denominator')
            self.num, self.den = a.num, a.den
            return
        a, b = Poly(a), Poly(b)
        require(bool(b), 'rational function denominator zero')
        if not a:
            self.num, self.den = Poly(), Poly(1)
            return
        g = polynomial_gcd(a, b)
        a, b = exact_quotient(a, g), exact_quotient(b, g)
        scale = 1
        for c in a.c+b.c:
            d = F(c).denominator; scale = scale*d//gcd(scale, d)
        aa, bb = [int(c*scale) for c in a.c], [int(c*scale) for c in b.c]
        common = reduce(gcd, aa+bb)
        if bb[-1] < 0: common = -common
        self.num, self.den = Poly([v//common for v in aa]), Poly([v//common for v in bb])
    def __bool__(self): return bool(self.num)
    def __eq__(self, b):
        b = Rat(b)
        return self.num*b.den == b.num*self.den
    def __add__(self, b):
        if isinstance(b, Sparse): return b+self
        b = Rat(b)
        return Rat(self.num*b.den+b.num*self.den, self.den*b.den)
    __radd__ = __add__
    def __neg__(self): return Rat(-self.num, self.den)
    def __sub__(self, b):
        if isinstance(b, Sparse): return -b+self
        return self+-Rat(b)
    def __rsub__(self, b): return Rat(b)+-self
    def __mul__(self, b):
        if isinstance(b, Sparse): return b*self
        b = Rat(b)
        return Rat(self.num*b.num, self.den*b.den)
    __rmul__ = __mul__
    def __truediv__(self, b):
        b = Rat(b)
        require(bool(b), 'division by zero rational function')
        return Rat(self.num*b.den, self.den*b.num)
    def __rtruediv__(self, b): return Rat(b)/self
    def __pow__(self, k):
        require(isinstance(k, int) and k >= 0, 'invalid rational power')
        return Rat(self.num**k, self.den**k)
    def shift(self, k=1): return Rat(self.num.shift(k), self.den.shift(k))
    def value(self, n):
        b = self.den.value(n)
        require(b != 0, 'rational evaluation at a pole')
        return F(self.num.value(n), b)
    def coefficients(self):
        return {'numerator': list(self.num.c), 'denominator': list(self.den.c)}


class Sparse:
    """Q(n)[t,x,y,w,j], where w represents t**n; coefficients are Rat."""
    ZERO = (0, 0, 0, 0, 0)
    def __init__(self, a=0):
        if isinstance(a, Sparse): self.terms = dict(a.terms)
        elif isinstance(a, dict):
            require(all(len(k)==5 and all(isinstance(i,int) and i>=0 for i in k) for k in a),
                    'invalid sparse exponent')
            self.terms = {k:Rat(v) for k,v in a.items() if Rat(v)}
        else:
            a = Rat(a); self.terms = {self.ZERO:a} if a else {}
    def __bool__(self): return bool(self.terms)
    def __eq__(self, b): return self.terms == Sparse(b).terms
    def __add__(self, b):
        b = Sparse(b); r = dict(self.terms)
        for k,v in b.terms.items(): r[k] = r.get(k,Rat())+v
        return Sparse(r)
    __radd__ = __add__
    def __neg__(self): return Sparse({k:-v for k,v in self.terms.items()})
    def __sub__(self,b): return self+-Sparse(b)
    def __rsub__(self,b): return Sparse(b)+-self
    def __mul__(self,b):
        b=Sparse(b);r={}
        for k,v in self.terms.items():
            for l,u in b.terms.items():
                e=tuple(i+j for i,j in zip(k,l));r[e]=r.get(e,Rat())+v*u
        return Sparse(r)
    __rmul__=__mul__
    def __truediv__(self,b): return self*(1/Rat(b))
    def __pow__(self,k):
        require(isinstance(k,int) and k>=0,'invalid sparse power')
        a,b=Sparse(1),self
        while k:
            if k&1:a=a*b
            k//=2
            if k:b=b*b
        return a
    def derivative(self,i):
        require(i in range(5),'unknown derivative variable')
        r={}
        for k,v in self.terms.items():
            if k[i]:
                l=list(k);l[i]-=1;r[tuple(l)]=v*k[i]
        return Sparse(r)
    def shift(self,k=1): return Sparse({e:v.shift(k) for e,v in self.terms.items()})
    def substitute(self,replacements):
        variables=[Sparse({tuple(int(i==j) for i in range(5)):1}) for j in range(5)]
        for i,v in replacements.items():variables[i]=Sparse(v)
        r=Sparse()
        for e,v in self.terms.items():
            term=Sparse(v)
            for i,k in enumerate(e):term*=variables[i]**k
            r+=term
        return r
    def scalar(self):
        require(all(e==self.ZERO for e in self.terms),'not a scalar')
        return self.terms.get(self.ZERO,Rat())


N=Rat(Poly([0,1]))
T,X,Y,W,J=[Sparse({tuple(int(i==j) for i in range(5)):1}) for j in range(5)]


def self_test():
    require((N+1)**3 == N**3+3*N*N+3*N+1,'rational expansion')
    require(Rat(Poly([-1,0,1]),Poly([-1,1])) == N+1,'rational cancellation')
    require((1/N).shift().value(2)==F(1,3),'rational shift')
    require((T+X)**2 == T*T+2*T*X+X*X,'sparse expansion')
    require((T*X**2*Y).derivative(1)==2*T*X*Y,'sparse derivative')
    require((T-X).substitute({0:X,1:T})==X-T,'simultaneous substitution')
    try: Rat(1,0)
    except ArithmeticError: pass
    else: raise ArithmeticError('zero denominator guard failed')
