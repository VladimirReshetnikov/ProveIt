"""Exact certificates and symbolic reductions for Gaussian harmonic polylogarithms.

Analytic justification: article.tex (signed kernels, parity, and Euler certificates).  No floating-point arithmetic
is used by the interval evaluator. SymPy is needed only for symbolic formulas.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from math import comb, factorial
from typing import Iterable

Q = Fraction

def _positive_integer(n: int, name: str) -> None:
    if isinstance(n, bool) or not isinstance(n, int) or n < 1:
        raise ValueError(f"{name} must be a positive integer")

@dataclass(frozen=True)
class Interval:
    lo: Q
    hi: Q
    def __post_init__(self) -> None:
        object.__setattr__(self, "lo", Q(self.lo))
        object.__setattr__(self, "hi", Q(self.hi))
        if self.lo > self.hi:
            raise ValueError("Reversed interval")
    def __add__(self, other: Interval | Q | int) -> Interval:
        y = other if isinstance(other, Interval) else Interval(Q(other), Q(other))
        return Interval(self.lo + y.lo, self.hi + y.hi)
    __radd__ = __add__
    def __neg__(self) -> Interval:
        return Interval(-self.hi, -self.lo)
    def __sub__(self, other: Interval | Q | int) -> Interval:
        return self + (-other if isinstance(other, Interval) else -Q(other))
    def __mul__(self, other: Interval | Q | int) -> Interval:
        y = other if isinstance(other, Interval) else Interval(Q(other), Q(other))
        p = [self.lo*y.lo, self.lo*y.hi, self.hi*y.lo, self.hi*y.hi]
        return Interval(min(p), max(p))
    __rmul__ = __mul__
    def __pow__(self, exponent: int) -> Interval:
        if not isinstance(exponent, int) or exponent < 0:
            raise ValueError("Only nonnegative integer powers are supported")
        result = Interval(Q(1), Q(1))
        base = self
        n = exponent
        while n:
            if n & 1:
                result = result * base
            base = base * base
            n >>= 1
        return result
    def overlaps(self, other: Interval) -> bool:
        return max(self.lo, other.lo) <= min(self.hi, other.hi)
    def outward(self, digits: int = 100) -> dict[str, str]:
        """Fixed-point decimal enclosure, rounded outward using integer division."""
        if digits < 0:
            raise ValueError("digits must be nonnegative")
        scale = 10**digits
        low = (self.lo.numerator * scale) // self.lo.denominator
        high = -((-self.hi.numerator * scale) // self.hi.denominator)
        def fmt(n: int) -> str:
            sign = "-" if n < 0 else ""
            x = str(abs(n)).zfill(digits + 1)
            return sign + (x[:-digits] + "." + x[-digits:] if digits else x)
        return {"lower": fmt(low), "upper": fmt(high)}

@lru_cache(maxsize=None)
def euler_weights(N: int) -> tuple[int, ...]:
    _positive_integer(N, "N")
    weight = 1 << N
    binomial = 1
    values = []
    for n in range(N):
        if n:
            binomial = binomial * (N - n + 1) // n
        weight -= binomial
        values.append((-1)**n * weight)
    return tuple(values)

def euler_sum(values: Iterable[Q]) -> Q:
    terms = tuple(values)
    if not terms:
        raise ValueError("At least one value is required")
    return sum((v*w for v, w in zip(terms, euler_weights(len(terms)))), Q(0))/(1 << len(terms))

@lru_cache(maxsize=128)
def gaussian_euler(a: int, b: int, N: int) -> Q:
    """Exact E_N(a,b) for Im Li_{a,b}(i,1)."""
    for value, name in [(a,"a"),(b,"b"),(N,"N")]:
        _positive_integer(value, name)
    harmonic = Q(0)
    values = []
    for n in range(N):
        if n:
            harmonic += Q(1, (2*n-1)**b) + Q(1, (2*n)**b)
        values.append(harmonic / (2*n+1)**a)
    return euler_sum(values)

def gaussian_interval(a: int, b: int, N: int = 400) -> Interval:
    value = gaussian_euler(a,b,N)
    bound = Q(1) if b == 1 else Q(b,b-1)
    return Interval(value-bound/(1 << N), value)

@lru_cache(maxsize=64)
def odd_harmonic_euler(p: int, N: int = 400) -> Q:
    """Euler approximant for S_p = sum (-1)^n H_n/(2n+1)^p."""
    _positive_integer(p, "p")
    _positive_integer(N, "N")
    H = Q(0)
    values = []
    for n in range(N):
        if n:
            H += Q(1, n)
        values.append(H / (2*n+1)**p)
    return euler_sum(values)

def odd_harmonic_interval(p: int, N: int = 400) -> Interval:
    """One-sided exact enclosure; tail <= (N+1)/(3**p * 2**N)."""
    value = odd_harmonic_euler(p, N)
    return Interval(value - Q(N+1, 3**p * (1 << N)), value)

@lru_cache(maxsize=None)
def beta_interval(s: int, N: int = 400) -> Interval:
    _positive_integer(s,"s")
    value = euler_sum(Q(1,(2*n+1)**s) for n in range(N))
    return Interval(value, value + Q(1,1 << N))

@lru_cache(maxsize=None)
def zeta_interval(s: int, N: int = 400) -> Interval:
    _positive_integer(s, "s")
    if s < 2:
        raise ValueError("zeta_interval requires an integer s >= 2")
    value = euler_sum(Q(1,(n+1)**s) for n in range(N))
    scale = Q(1)/(1-Q(2)**(1-s))
    return Interval(value, value+Q(1,1 << N))*scale

@lru_cache(maxsize=None)
def log2_interval(N: int = 400) -> Interval:
    _positive_integer(N, "N")
    value = 2*sum((Q(1,(2*n+1)*3**(2*n+1)) for n in range(N)), Q(0))
    tail = Q(9,4*(2*N+1)*3**(2*N+1))
    return Interval(value,value+tail)

@lru_cache(maxsize=None)
def pi_interval(N: int = 400) -> Interval:
    _positive_integer(N, "N")
    def atan_inverse(q: int) -> Interval:
        value = sum((Q((-1)**n,(2*n+1)*q**(2*n+1)) for n in range(N)), Q(0))
        nxt = Q((-1)**N,(2*N+1)*q**(2*N+1))
        return Interval(min(value,value+nxt),max(value,value+nxt))
    return 16*atan_inverse(5)-4*atan_inverse(239)

# Symbolic functions use formal atoms to avoid unproved independence assumptions.
def atoms():
    import sympy as s
    return s.Symbol("pi",real=True), s.Symbol("L",real=True)

def zeta_symbol(n: int):
    import sympy as s
    pi,_ = atoms()
    return s.zeta(n).subs(s.pi,pi) if n % 2 == 0 else s.Symbol(f"Z{n}",real=True)

def beta_symbol(n: int):
    import sympy as s
    pi,_ = atoms()
    if n % 2:
        return s.Rational((-1)**((n-1)//2)*int(s.euler(n-1)),4**((n+1)//2)*factorial(n-1))*pi**n
    return s.Symbol(f"B{n}",real=True)

def single_symbol(n: int, color: int):
    """Li_n(i**color), excluding the divergent Li_1(1)."""
    import sympy as s
    _,L = atoms()
    r = color % 4
    if r == 0:
        if n == 1:
            raise ValueError("Li_1(1) diverges")
        return zeta_symbol(n)
    eta = L if n == 1 else (1-s.Rational(2)**(1-n))*zeta_symbol(n)
    if r == 2:
        return -eta
    return -eta/2**n + (s.I if r == 1 else -s.I)*beta_symbol(n)

def parity_symbol(a: int, b: int):
    """Even weight: Im Li_{a,b}(i,1); odd weight: Re Li_{a,b}(i,1)."""
    import sympy as s
    for value,name in [(a,"a"),(b,"b")]:
        _positive_integer(value,name)
    pi,_=atoms(); w=a+b
    B=lambda k:(2*s.I*pi)**k*s.bernoulli(k,s.Rational(1,4))/factorial(k)
    p=sum((-1)**(b+m)*comb(m-1,b-1)*zeta_symbol(m)*B(w-m)
          for m in range(b+1,w+1))
    p-=single_symbol(w,1)
    p+=(-1)**a*sum(comb(m-1,a-1)*single_symbol(m,3)*B(w-m)
                   for m in range(a,w+1))
    return s.expand(s.im(p)/2 if w % 2 == 0 else s.re(p)/2)

def symbolic_interval(expression, N: int = 400) -> Interval:
    import sympy as s
    if expression.is_Rational:
        q=Q(int(expression.p),int(expression.q))
        return Interval(q,q)
    if expression.is_Symbol:
        name=str(expression)
        # Conservative term allocation: 5**2 > 2**4 and 3**2 > 2**3.
        # These primitive errors are smaller than 2**(-N), without needless
        # over-resolution of the much faster arctangent/logarithm series.
        if name == "pi": return pi_interval((N+3)//4+8)
        if name == "L": return log2_interval((N+2)//3+8)
        if name.startswith("B"): return beta_interval(int(name[1:]),N)
        if name.startswith("Z"): return zeta_interval(int(name[1:]),N)
        raise ValueError(f"Unknown atom: {name}")
    if expression.is_Add:
        return sum((symbolic_interval(x,N) for x in expression.args),Interval(Q(0),Q(0)))
    if expression.is_Mul:
        out=Interval(Q(1),Q(1))
        for x in expression.args: out=out*symbolic_interval(x,N)
        return out
    if expression.is_Pow and expression.exp.is_Integer and expression.exp>=0:
        return symbolic_interval(expression.base,N)**int(expression.exp)
    raise ValueError(f"Unsupported expression: {expression}")

def shuffle_matrix(w: int):
    import sympy as s
    _positive_integer(w, "w")
    if w < 2: raise ValueError("Weight must be at least 2")
    def c(n,k): return comb(n,k) if 0<=k<=n else 0
    return s.Matrix([[c(a-1,p-1)+c(a-1,w-p-1) for a in range(1,w)]
                     for p in range(1,w//2+1)])

def kernel_polynomial(a: int,b: int):
    """P_ab(T) in the signed density kappa_ab(exp(-T))."""
    _positive_integer(a, "a")
    _positive_integer(b, "b")
    import sympy as s
    T=s.Symbol("T",positive=True);w=a+b
    out=-T**(w-1)/factorial(w-1)
    out+=sum((-1)**(m-b-1)*comb(m-1,b-1)*s.zeta(m)*T**(w-1-m)/factorial(w-1-m)
             for m in range(b+1,w))
    return T,s.expand(out)

def kernel_exact(a: int,b: int):
    import sympy as s
    T,P=kernel_polynomial(a,b);w=a+b
    out=P+(-1)**(a-1)*sum(comb(w-j-2,a-1)*T**j/factorial(j)*s.polylog(w-1-j,s.exp(-T))
                         for j in range(b))
    return T,out

