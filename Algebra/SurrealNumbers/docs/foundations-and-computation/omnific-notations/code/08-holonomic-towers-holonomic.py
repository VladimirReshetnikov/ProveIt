"""Exact certified Euler series over Q and a guarded omnific subring.

This is a finite prototype for the accompanying article, not a general
surreal implementation. Dependencies: Python >= 3.10, SymPy >= 1.12.
A certificate L = sum t**j P_j(theta) uses theta = t*d/dt. Its jet includes
every coefficient through the largest nonnegative integer root of P_0.
No floating-point arithmetic, numerical zero tests, or analytic convergence
assumptions are used. General higher-rank field coefficients are not implemented.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import cached_property
from typing import Callable, Iterable
import sympy as s
from sympy.functions.combinatorial.numbers import stirling

X, t = s.symbols('X t')


def q(value):
    """Reject floating-point input; accept only exact rational values."""
    value = s.sympify(value)
    if not value.is_Rational:
        raise TypeError(f'Expected an exact rational, received {value!r}')
    return s.Rational(value)


def integer_roots(poly: s.Poly) -> list[int]:
    if poly.is_zero:
        raise ValueError('The initial Euler polynomial must be nonzero')
    return sorted(int(r) for r in s.polys.polytools.ground_roots(poly)
                  if r.is_Integer and r >= 0)


def falling_poly(k: int):
    return s.prod(X-j for j in range(k))


def differential_to_euler(coeffs: Iterable) -> tuple[s.Poly, ...]:
    """Convert sum coeffs[i](t)*D**i to normalized sum t**j*P_j(theta)."""
    coeffs = [s.cancel(c) for c in coeffs]
    denominator = s.lcm([s.denom(c) for c in coeffs])
    blocks = {}
    for i, c in enumerate(coeffs):
        polynomial = s.Poly(s.cancel(c*denominator), t, domain=s.QQ)
        for (power,), a in polynomial.terms():
            if a:
                exponent = power-i
                blocks[exponent] = blocks.get(exponent, 0) + a*falling_poly(i)
    blocks = {j: s.expand(p) for j, p in blocks.items() if s.expand(p) != 0}
    if not blocks:
        raise ValueError('Zero differential operator')
    lo, hi = min(blocks), max(blocks)
    polys = [s.Poly(blocks.get(j, 0), X, domain=s.QQ) for j in range(lo, hi+1)]
    # Rational scalar normalization makes operators reproducible without
    # claiming they are minimal annihilators.
    scale = polys[0].LC()
    return tuple(s.Poly(p.as_expr()/scale, X, domain=s.QQ) for p in polys)


class Holonomic:
    """A validated rational Euler certificate and its uniquely selected series."""

    def __init__(self, polynomials: Iterable, jet: Iterable):
        ps = [s.Poly(p, X, domain=s.QQ) for p in polynomials]
        while ps and ps[-1].is_zero:
            ps.pop()
        if not ps or ps[0].is_zero:
            raise ValueError('P_0 must be nonzero and leading t exponent must be zero')
        self.polynomials = tuple(ps)
        roots = integer_roots(ps[0])
        self.bound = max(roots, default=-1)
        self.jet = tuple(q(c) for c in jet)
        if len(self.jet) != self.bound+1:
            raise ValueError(f'Expected {self.bound+1} jet entries, got {len(self.jet)}')
        for n in range(self.bound+1):
            residual = sum(ps[j].eval(n-j)*self.jet[n-j]
                           for j in range(min(n, len(ps)-1)+1))
            if residual:
                raise ValueError(f'Incompatible jet: recurrence residual at {n} is {residual}')
        self._coefficients = list(self.jet)

    @classmethod
    def selected(cls, polynomials: Iterable, coefficient: Callable[[int], object]):
        ps = tuple(s.Poly(p, X, domain=s.QQ) for p in polynomials)
        B = max(integer_roots(ps[0]), default=-1)
        return cls(ps, [coefficient(n) for n in range(B+1)])

    @classmethod
    def constant(cls, value=0):
        return cls([X], [q(value)])

    @classmethod
    def monomial(cls, degree: int, coefficient=1):
        if not isinstance(degree, int) or degree < 0:
            raise ValueError('Power-series degree must be a nonnegative integer')
        coefficient = q(coefficient)
        return cls([X-degree], [0]*degree + [coefficient])

    @property
    def is_zero(self) -> bool:
        return all(c == 0 for c in self.jet)

    @property
    def valuation(self) -> int:
        if self.is_zero:
            raise ValueError('Zero has no finite Laurent valuation')
        return next(n for n, c in enumerate(self.jet) if c)

    @property
    def leading_coefficient(self):
        return self.jet[self.valuation]

    def coefficient(self, n: int):
        if not isinstance(n, int):
            raise TypeError('Coefficient index must be an integer')
        if n < 0:
            return s.S.Zero
        ps = self.polynomials
        while len(self._coefficients) <= n:
            m = len(self._coefficients)
            denom = ps[0].eval(m)
            if denom == 0:  # Constructor should have supplied all singular indices.
                raise ArithmeticError('Missing singular coefficient in validated certificate')
            numer = sum(ps[j].eval(m-j)*self._coefficients[m-j]
                        for j in range(1, min(m, len(ps)-1)+1))
            self._coefficients.append(q(-numer/denom))
        return self._coefficients[n]

    @cached_property
    def differential_coefficients(self):
        order = max((p.degree() for p in self.polynomials if not p.is_zero), default=0)
        result = [s.S.Zero]*(order+1)
        for j, p in enumerate(self.polynomials):
            for (k,), a in p.terms():
                for i in range(k+1):
                    result[i] += a*stirling(k, i, kind=2)*t**(j+i)
        return tuple(s.expand(c) for c in result)

    def companion(self):
        cs = self.differential_coefficients
        r = len(cs)-1
        if r < 1:
            raise ValueError('An order-zero operator has no nonzero series solution')
        A = s.zeros(r)
        for i in range(r-1):
            A[i, i+1] = 1
        for i in range(r):
            A[r-1, i] = s.cancel(-cs[i]/cs[r])
        return A

    @staticmethod
    def _annihilator(A: s.Matrix, first: s.Matrix):
        rows = []
        row = first
        for _ in range(A.rows+1):
            rows.append(row)
            stacked = s.Matrix.vstack(*rows)
            dependencies = stacked.T.nullspace()
            if dependencies:
                relation = next(v for v in dependencies if v[-1] != 0)
                return differential_to_euler(relation)
            row = (row.diff(t)+row*A).applyfunc(s.cancel)
        raise ArithmeticError('Finite-dimensional row dependence was not found')

    def __neg__(self):
        return Holonomic(self.polynomials, [-a for a in self.jet])

    def __add__(self, other):
        if not isinstance(other, Holonomic):
            other = Holonomic.constant(other)
        if self.is_zero:
            return other
        if other.is_zero:
            return self
        A, B = self.companion(), other.companion()
        matrix = s.diag(A, B)
        output = s.zeros(1, matrix.rows)
        output[0, 0] = output[0, A.rows] = 1
        ps = self._annihilator(matrix, output)
        return Holonomic.selected(ps, lambda n: self.coefficient(n)+other.coefficient(n))

    __radd__ = __add__

    def __sub__(self, other):
        return self + (-other if isinstance(other, Holonomic) else -q(other))

    def __mul__(self, other):
        if not isinstance(other, Holonomic):
            other = Holonomic.constant(other)
        if self.is_zero or other.is_zero:
            return Holonomic.constant(0)
        A, B = self.companion(), other.companion()
        matrix = s.kronecker_product(A, s.eye(B.rows)) + s.kronecker_product(s.eye(A.rows), B)
        output = s.zeros(1, matrix.rows)
        output[0, 0] = 1
        ps = self._annihilator(matrix, output)
        return Holonomic.selected(ps, lambda n: sum(self.coefficient(j)*other.coefficient(n-j)
                                                    for j in range(n+1)))

    __rmul__ = __mul__

    def equal(self, other) -> bool:
        return (self-other).is_zero

    def summary(self):
        return {'operator': [str(p.as_expr()) for p in self.polynomials],
                'exceptional_bound': self.bound,
                'jet': [str(a) for a in self.jet], 'zero': self.is_zero}


@dataclass(frozen=True)
class HF:
    """Fraction of certified power series, embedded in Q((t))."""
    numerator: Holonomic
    denominator: Holonomic

    def __post_init__(self):
        if self.denominator.is_zero:
            raise ZeroDivisionError('Zero denominator')

    @classmethod
    def of(cls, value):
        if isinstance(value, HF):
            return value
        if not isinstance(value, Holonomic):
            value = Holonomic.constant(value)
        return cls(value, Holonomic.constant(1))

    @classmethod
    def monomial(cls, n: int):
        if not isinstance(n, int):
            raise TypeError('Laurent exponent must be an integer')
        return (cls.of(Holonomic.monomial(n)) if n >= 0
                else cls(Holonomic.constant(1), Holonomic.monomial(-n)))

    @property
    def is_zero(self):
        return self.numerator.is_zero

    @property
    def valuation(self):
        return self.numerator.valuation-self.denominator.valuation

    @property
    def leading_coefficient(self):
        return self.numerator.leading_coefficient/self.denominator.leading_coefficient

    @property
    def sign(self):
        return 0 if self.is_zero else int(s.sign(self.leading_coefficient))

    def coefficient(self, n: int):
        if not isinstance(n, int):
            raise TypeError('Laurent index must be an integer')
        if self.is_zero:
            return s.S.Zero
        v, b = self.valuation, self.denominator.valuation
        if n < v:
            return s.S.Zero
        values = {}
        q0 = self.denominator.coefficient(b)
        for m in range(v, n+1):
            correction = sum(self.denominator.coefficient(b+j)*values[m-j]
                             for j in range(1, m-v+1))
            values[m] = q((self.numerator.coefficient(m+b)-correction)/q0)
        return values[n]

    def __neg__(self):
        return HF(-self.numerator, self.denominator)

    def __add__(self, other):
        other = HF.of(other)
        if self.is_zero:
            return other
        if other.is_zero:
            return self
        return HF(self.numerator*other.denominator + other.numerator*self.denominator,
                  self.denominator*other.denominator)

    __radd__ = __add__

    def __sub__(self, other):
        return self + (-HF.of(other))

    def __mul__(self, other):
        other = HF.of(other)
        return HF(self.numerator*other.numerator, self.denominator*other.denominator)

    __rmul__ = __mul__

    def inverse(self):
        if self.is_zero:
            raise ZeroDivisionError('Cannot invert zero')
        return HF(self.denominator, self.numerator)

    def __truediv__(self, other):
        return self*HF.of(other).inverse()

    def equal(self, other) -> bool:
        other = HF.of(other)
        return (self.numerator*other.denominator-other.numerator*self.denominator).is_zero


class Guarded:
    """Z + U*HF[U], where U=omega**omega and t=omega**(-1).

    This is a subring of R_2, not the entire R_2: its constant term is an
    ordinary integer rather than an arbitrary member of R_1.
    """
    def __init__(self, constant: int = 0, blocks: dict[int, HF] | None = None):
        if not isinstance(constant, int):
            raise TypeError('Guarded constant must be an ordinary Python integer')
        self.constant = constant
        self.blocks = {}
        for k, f in (blocks or {}).items():
            if not isinstance(k, int) or k < 1:
                raise ValueError('Guard block degree must be a positive integer')
            f = HF.of(f)
            if not f.is_zero:
                self.blocks[k] = f

    def __neg__(self):
        return Guarded(-self.constant, {k: -f for k, f in self.blocks.items()})

    def __add__(self, other):
        if not isinstance(other, Guarded):
            other = Guarded(other)
        blocks = dict(self.blocks)
        for k, f in other.blocks.items():
            blocks[k] = blocks.get(k, HF.of(0)) + f
        return Guarded(self.constant+other.constant, blocks)

    __radd__ = __add__

    def __sub__(self, other):
        return self + (-other if isinstance(other, Guarded) else -other)

    def __mul__(self, other):
        if not isinstance(other, Guarded):
            other = Guarded(other)
        blocks = {}
        def add(k, f):
            blocks[k] = blocks.get(k, HF.of(0)) + f
        for k, f in self.blocks.items():
            if other.constant:
                add(k, f*other.constant)
        for k, f in other.blocks.items():
            if self.constant:
                add(k, f*self.constant)
        for k, f in self.blocks.items():
            for j, g in other.blocks.items():
                add(k+j, f*g)
        return Guarded(self.constant*other.constant, blocks)

    __rmul__ = __mul__

    def equal(self, other):
        if not isinstance(other, Guarded):
            other = Guarded(other)
        if self.constant != other.constant:
            return False
        return all(self.blocks.get(k, HF.of(0)).equal(other.blocks.get(k, HF.of(0)))
                   for k in self.blocks.keys() | other.blocks.keys())

    @property
    def leading(self):
        """Return ((k,m),c), meaning c*omega**(k*omega+m), or None for zero."""
        if self.blocks:
            k = max(self.blocks)
            f = self.blocks[k]
            return ((k, -f.valuation), f.leading_coefficient)
        if self.constant:
            return ((0, 0), s.Integer(self.constant))
        return None

    @property
    def sign(self):
        leading = self.leading
        return 0 if leading is None else int(s.sign(leading[1]))
