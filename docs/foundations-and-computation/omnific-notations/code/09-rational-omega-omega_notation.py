"""Exact finite rational/Conway-omega expressions; research prototype.

Python >= 3.9; SymPy >= 1.12, < 2. No floating-point arithmetic.
The meaning of om(x) is Conway's omega map, not exp(x*log(omega)).
Equality is exposed as equivalent(), not Python object equality.
The sparse-fraction core uses only fractions and finite recursion. SymPy is
used solely for polynomial division after the separated-grid conversion.
"""
from dataclasses import dataclass
from fractions import Fraction
from functools import cmp_to_key
from math import gcd
from typing import Optional, Tuple, List, Sequence
import sympy as sp


@dataclass(frozen=True, eq=False)
class Value:
    level: int
    scalar: Optional[Fraction] = None
    numerator: tuple = ()
    denominator: tuple = ()

    def __add__(self, other): return add(self, number(other))
    def __radd__(self, other): return add(number(other), self)
    def __neg__(self): return scale(self, Fraction(-1))
    def __sub__(self, other): return add(self, -number(other))
    def __rsub__(self, other): return add(number(other), -self)
    def __mul__(self, other): return multiply(self, number(other))
    def __rmul__(self, other): return multiply(number(other), self)
    def __truediv__(self, other): return divide(self, number(other))
    def __rtruediv__(self, other): return divide(number(other), self)
    def __pow__(self, n):
        if not isinstance(n, int):
            raise TypeError('Only integer powers are accepted; use om() explicitly.')
        if n < 0: return (number(1) / self) ** (-n)
        ans, base = number(1), self
        while n:
            if n & 1: ans = ans * base
            n >>= 1
            if n: base = base * base
        return ans

    def __bool__(self):
        raise TypeError('Use is_zero(), equivalent(), or compare().')

    def __repr__(self):
        if self.level == 0: return str(self.scalar)
        def poly(p):
            return ' + '.join('%s*om(%r)' % (c, e) for e, c in p) or '0'
        return '(%s)/(%s)' % (poly(self.numerator), poly(self.denominator))


def number(x=0) -> Value:
    if isinstance(x, Value): return x
    if isinstance(x, float):
        raise TypeError('Use Fraction or integers, not a floating-point literal.')
    return Value(0, Fraction(x))


def zero(level=0): return promote(number(0), level)
def one(level=0): return promote(number(1), level)


def promote(x: Value, level: int) -> Value:
    if level < x.level: raise ValueError('Cannot lower the representation level.')
    if level == x.level: return x
    if x.level == 0:
        unit = ((zero(level - 1), Fraction(1)),)
        p = () if x.scalar == 0 else ((zero(level - 1), x.scalar),)
        return Value(level, None, p, unit)
    def lift(p): return tuple((promote(e, level-1), c) for e, c in p)
    return Value(level, None, lift(x.numerator), lift(x.denominator))


def is_zero(x: Value) -> bool:
    return x.scalar == 0 if x.level == 0 else not x.numerator


def sign(x: Value) -> int:
    if is_zero(x): return 0
    c = x.scalar if x.level == 0 else x.numerator[0][1]
    # Denominators always have positive leading coefficient 1.
    return 1 if c > 0 else -1


def collect(terms):
    terms = [(e, Fraction(c)) for e, c in terms if c != 0]
    terms.sort(key=cmp_to_key(lambda a, b: -compare(a[0], b[0])))
    out = []
    for e, c in terms:
        if out and equivalent(out[-1][0], e):
            olde, oldc = out.pop()
            if oldc + c: out.append((olde, oldc + c))
        else: out.append((e, c))
    return tuple(out)


def poly_equal(p, q):
    return len(p) == len(q) and all(c == d and equivalent(e, f)
                                   for (e, c), (f, d) in zip(p, q))


def poly_mul(p, q):
    return collect((e + f, c*d) for e, c in p for f, d in q)


def make(level, p, q):
    p, q = collect(p), collect(q)
    if not q: raise ZeroDivisionError('Zero denominator in an omega expression.')
    if not p: return zero(level)
    if poly_equal(p, q): return one(level)
    e0, c0 = q[0]
    # A common monomial division preserves the value and simplifies leaders.
    def normal(t): return tuple((e - e0, c / c0) for e, c in t)
    return Value(level, None, normal(p), normal(q))


def aligned(x, y):
    d = max(x.level, y.level)
    return promote(x, d), promote(y, d), d


def add(x, y):
    x, y, d = aligned(x, y)
    if d == 0: return number(x.scalar + y.scalar)
    if is_zero(x): return y
    if is_zero(y): return x
    if poly_equal(x.denominator, y.denominator):
        return make(d, x.numerator + y.numerator, x.denominator)
    return make(d, poly_mul(x.numerator, y.denominator) +
                poly_mul(y.numerator, x.denominator),
                poly_mul(x.denominator, y.denominator))


def scale(x, c):
    c = Fraction(c)
    if x.level == 0: return number(x.scalar * c)
    return make(x.level, tuple((e, a*c) for e, a in x.numerator), x.denominator)


def multiply(x, y):
    x, y, d = aligned(x, y)
    if d == 0: return number(x.scalar*y.scalar)
    if is_zero(x) or is_zero(y): return zero(d)
    return make(d, poly_mul(x.numerator, y.numerator),
                poly_mul(x.denominator, y.denominator))


def divide(x, y):
    if is_zero(y): raise ZeroDivisionError('Division by zero.')
    x, y, d = aligned(x, y)
    if d == 0: return number(x.scalar/y.scalar)
    return make(d, poly_mul(x.numerator, y.denominator),
                poly_mul(x.denominator, y.numerator))


def equivalent(x, y) -> bool:
    x, y, d = aligned(number(x), number(y))
    if d == 0: return x.scalar == y.scalar
    if poly_equal(x.denominator, y.denominator):
        return poly_equal(x.numerator, y.numerator)
    return poly_equal(poly_mul(x.numerator, y.denominator),
                      poly_mul(y.numerator, x.denominator))


def compare(x, y) -> int:
    x, y = number(x), number(y)
    if x is y: return 0
    return sign(x-y)


def om(x) -> Value:
    x = number(x)
    return make(x.level+1, ((x, Fraction(1)),),
                ((zero(x.level), Fraction(1)),))


def leading(x: Value):
    """Return (growth exponent, rational leading coefficient); x must be nonzero."""
    if is_zero(x): raise ValueError('Zero has no leading exponent.')
    if x.level == 0: return number(0), x.scalar
    ep, cp = x.numerator[0]
    eq, cq = x.denominator[0]
    return ep-eq, cp/cq


def separated_basis(values: Sequence[Value]) -> List[Value]:
    """A positive Q-basis, ordered by decreasing Archimedean magnitude."""
    remaining = [v for v in values if not is_zero(v)]
    result = []
    while remaining:
        pivot = max(remaining, key=cmp_to_key(
            lambda a, b: compare(leading(a)[0], leading(b)[0])))
        if sign(pivot) < 0: pivot = -pivot
        pe, pc = leading(pivot)
        result.append(pivot)
        new = []
        for v in remaining:
            ve, vc = leading(v)
            if equivalent(ve, pe): v = v - scale(pivot, vc/pc)
            if not is_zero(v): new.append(v)
        remaining = new
    return result


def coordinates(v: Value, basis: Sequence[Value]):
    out = []
    for b in basis:
        c = Fraction(0)
        if not is_zero(v):
            ve, vc = leading(v)
            be, bc = leading(b)
            if equivalent(ve, be):
                c = vc/bc
                v = v-scale(b, c)
        out.append(c)
    if not is_zero(v): raise ArithmeticError('Basis did not span the supplied exponent.')
    return out


def grid_form(x: Value):
    """Return (SymPy rational function, variables, positive separated exponents)."""
    if x.level == 0:
        return sp.Rational(x.scalar.numerator, x.scalar.denominator), (), ()
    terms = x.numerator + x.denominator
    basis = separated_basis([e for e, _ in terms])
    coords = [coordinates(e, basis) for e, _ in terms]
    n = 1
    for row in coords:
        for c in row: n = n*c.denominator // gcd(n, c.denominator)
    gamma = tuple(scale(b, Fraction(1, n)) for b in basis)
    variables = tuple(sp.symbols('X0:%d' % len(basis)))
    def polynomial(ts):
        out = sp.S.Zero
        for e, c in ts:
            mon = sp.Rational(c.numerator, c.denominator)
            for var, a in zip(variables, coordinates(e, basis)):
                k = a*n
                if k.denominator != 1: raise ArithmeticError('Uncleared coordinate.')
                mon *= var**int(k)
            out += mon
        return out
    return sp.cancel(polynomial(x.numerator)/polynomial(x.denominator)), variables, gamma


def rational_truncation(expr, variables):
    """Keep nonnegative lexicographic exponent vectors; also return coefficient 0."""
    expr = sp.cancel(expr)
    if not variables:
        if not expr.is_Rational: raise TypeError('Expected a rational constant.')
        return expr, expr
    v, tail = variables[0], variables[1:]
    p, q = sp.fraction(expr)
    domain = sp.QQ.frac_field(*tail) if tail else sp.QQ
    pp, qq = sp.Poly(p, v, domain=domain), sp.Poly(q, v, domain=domain)
    quotient, _ = pp.div(qq)
    c0 = quotient.nth(0)
    pos = quotient.as_expr()-c0
    truncated_c0, constant = rational_truncation(c0, tail)
    return sp.cancel(pos+truncated_c0), constant


def evaluate_rational(expr, variables, gamma):
    if not variables:
        r = sp.Rational(expr)
        return number(Fraction(int(r.p), int(r.q)))
    values = tuple(om(g) for g in gamma)
    p, q = sp.fraction(sp.cancel(expr))
    def evaluate(poly):
        ans = number(0)
        for powers, c in sp.Poly(poly, *variables, domain=sp.QQ).terms():
            term = number(Fraction(int(c.p), int(c.q)))
            for v, n in zip(values, powers): term = term*(v**n)
            ans = ans+term
        return ans
    return evaluate(p)/evaluate(q)


def nonnegative_part(x: Value):
    """Return (sum at growth exponents >= 0, rational constant coefficient)."""
    expr, variables, gamma = grid_form(x)
    trunc, c = rational_truncation(expr, variables)
    return evaluate_rational(trunc, variables, gamma), Fraction(int(c.p), int(c.q))


def is_omnific(x: Value) -> bool:
    trunc, c = nonnegative_part(x)
    return c.denominator == 1 and equivalent(x, trunc)


def omnific_floor(x: Value) -> Value:
    trunc, c = nonnegative_part(x)
    k = c.numerator // c.denominator
    if c.denominator == 1 and sign(x-trunc) < 0: k -= 1
    return trunc-number(c)+number(k)


def truncate_at(x: Value, exponent: Value) -> Value:
    monomial = om(exponent)
    truncated, _ = nonnegative_part(x/monomial)
    return monomial*truncated


def coefficient_at(x: Value, exponent: Value) -> Fraction:
    _, c = nonnegative_part(x/om(exponent))
    return c
