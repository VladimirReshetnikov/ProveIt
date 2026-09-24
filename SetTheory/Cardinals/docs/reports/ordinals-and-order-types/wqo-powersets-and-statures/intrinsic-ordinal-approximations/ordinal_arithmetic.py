"""Exact Cantor-normal-form arithmetic for ordinals below epsilon_0.

No floating-point approximations or symbolic CAS are used.  Supported operations:
ordinary addition, Hessenberg natural sum/product, omega exponentiation, the
finite Milner--Rado sum, and a cofinal predecessor sampler.  The sampler is for
experiments; a finite sample does not establish a transfinite supremum.

Run ``python verify.py`` for the accompanying tests.  Python 3.10+; stdlib only.
"""
from __future__ import annotations

from dataclasses import dataclass
from functools import total_ordering
from typing import Iterable


@total_ordering
@dataclass(frozen=True)
class Ordinal:
    """An ordinal below epsilon_0, in strictly descending Cantor normal form."""
    terms: tuple[tuple["Ordinal", int], ...] = ()

    def __post_init__(self) -> None:
        if not isinstance(self.terms, tuple):
            raise TypeError("terms must be a tuple")
        previous: Ordinal | None = None
        for exponent, coefficient in self.terms:
            if not isinstance(exponent, Ordinal):
                raise TypeError("each exponent must be an Ordinal")
            if type(coefficient) is not int or coefficient <= 0:
                raise ValueError("CNF coefficients must be positive integers")
            if previous is not None and not exponent < previous:
                raise ValueError("CNF exponents must strictly decrease")
            previous = exponent

    @classmethod
    def finite(cls, n: int) -> "Ordinal":
        if type(n) is not int or n < 0:
            raise ValueError("a finite ordinal must be a nonnegative integer")
        return cls() if n == 0 else cls(((cls(), n),))

    def __bool__(self) -> bool:
        return bool(self.terms)

    def __lt__(self, other: object) -> bool:
        if not isinstance(other, Ordinal):
            return NotImplemented
        for (e, c), (f, d) in zip(self.terms, other.terms):
            if e != f:
                return e < f
            if c != d:
                return c < d
        return len(self.terms) < len(other.terms)

    def __add__(self, other: object) -> "Ordinal":
        """Ordinary, noncommutative ordinal addition."""
        if not isinstance(other, Ordinal):
            return NotImplemented
        if not other:
            return self
        leading, coefficient = other.terms[0]
        kept = [(e, c) for e, c in self.terms if e > leading]
        at_leading = next((c for e, c in self.terms if e == leading), 0)
        return Ordinal(tuple(kept + [(leading, at_leading + coefficient)]
                             + list(other.terms[1:])))

    def successor(self) -> "Ordinal":
        return self + ONE

    def __str__(self) -> str:
        if not self:
            return "0"
        out = []
        for exponent, coefficient in self.terms:
            if not exponent:
                out.append(str(coefficient))
            else:
                monomial = "w" if exponent == ONE else f"w^({exponent})"
                out.append(monomial if coefficient == 1
                           else f"{monomial}*{coefficient}")
        return " + ".join(out)


ZERO = Ordinal()
ONE = Ordinal.finite(1)
OMEGA = Ordinal(((ONE, 1),))


def cnf(*terms: tuple[Ordinal | int, int]) -> Ordinal:
    """Build a CNF; integer exponents are converted to finite ordinals."""
    return Ordinal(tuple((Ordinal.finite(e) if isinstance(e, int) else e, c)
                         for e, c in terms))


def omega_power(exponent: Ordinal) -> Ordinal:
    if not isinstance(exponent, Ordinal):
        raise TypeError("exponent must be an Ordinal")
    return Ordinal(((exponent, 1),))


def natural_sum(*args: Ordinal) -> Ordinal:
    coefficients: dict[Ordinal, int] = {}
    for a in args:
        if not isinstance(a, Ordinal):
            raise TypeError("natural_sum requires ordinals")
        for exponent, coefficient in a.terms:
            coefficients[exponent] = coefficients.get(exponent, 0) + coefficient
    return Ordinal(tuple(sorted(coefficients.items(), reverse=True)))


def natural_product(*args: Ordinal) -> Ordinal:
    """Natural product; the empty product is 1."""
    result = ONE
    for a in args:
        if not isinstance(a, Ordinal):
            raise TypeError("natural_product requires ordinals")
        coefficients: dict[Ordinal, int] = {}
        for e, c in result.terms:
            for f, d in a.terms:
                degree = natural_sum(e, f)
                coefficients[degree] = coefficients.get(degree, 0) + c * d
        result = Ordinal(tuple(sorted(coefficients.items(), reverse=True)))
    return result


def milner_rado(*args: Ordinal) -> Ordinal:
    """Milner--Rado sum of a nonempty finite sequence, by the classical CNF rule.

    If any argument is zero the result is zero.  Reject an empty sequence,
    rather than silently assigning a convention not used in the article.
    """
    if not args:
        raise ValueError("Milner--Rado sum requires at least one argument")
    if any(not isinstance(a, Ordinal) for a in args):
        raise TypeError("Milner--Rado sum requires ordinals")
    if any(not a for a in args):
        return ZERO
    tau = max(a.terms[-1][0] for a in args)
    k = sum(a.terms[-1][0] == tau for a in args)
    c = sum(coefficient for a in args for exponent, coefficient in a.terms
            if exponent == tau)
    high = natural_sum(*(Ordinal(tuple((e, v) for e, v in a.terms if e > tau))
                         for a in args))
    return Ordinal(high.terms + ((tau, c - k + 1),))


def predecessor_sample(a: Ordinal, n: int) -> Ordinal:
    """A predecessor, cofinal as n -> infinity for a nonzero limit ordinal.

    For a successor, return its largest predecessor. n must be positive.
    """
    if not isinstance(a, Ordinal):
        raise TypeError("a must be an Ordinal")
    if not a or type(n) is not int or n <= 0:
        raise ValueError("requires a positive ordinal and positive integer n")
    exponent, coefficient = a.terms[-1]
    prefix = list(a.terms[:-1])
    if coefficient > 1:
        prefix.append((exponent, coefficient - 1))
    base = Ordinal(tuple(prefix))
    if not exponent:
        return base
    lower_exponent = predecessor_sample(exponent, n)
    return base + Ordinal(((lower_exponent, n),))


def monomial_product_height(open_exponents: Iterable[Ordinal],
                            closed_exponents: Iterable[Ordinal],
                            finite_factors: Iterable[int] = ()) -> Ordinal:
    """h(P_f(A)) for the monomial product family proved in the article.

    An open exponent b denotes the ordinal factor w^b; a closed exponent c
    denotes w^c + 1.  All exponents must be positive.  Positive finite factors
    denote ordinary finite chains.  A zero finite factor makes A empty.
    With no factors, A is the one-point empty Cartesian product, hence height 2.
    """
    opened, closed, finite = (tuple(open_exponents), tuple(closed_exponents),
                              tuple(finite_factors))
    if any(not isinstance(a, Ordinal) or not a for a in opened + closed):
        raise ValueError("monomial exponents must be positive ordinals")
    if any(type(n) is not int or n < 0 for n in finite):
        raise ValueError("finite factors must be nonnegative integers")
    if any(n == 0 for n in finite):
        return ONE
    if opened:
        exponent = milner_rado(*(opened + tuple(c.successor() for c in closed)))
        return omega_power(exponent)
    coefficient = 1
    for n in finite:
        coefficient *= n
    return Ordinal(((natural_sum(*closed), coefficient),)).successor()
