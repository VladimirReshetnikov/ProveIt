#!/usr/bin/env python3
"""Exact finite-jet checks accompanying article.tex.

These checks do not prove the arbitrary-rank Hahn summability, global
classification, or analytic existence theorems.  They check identities in
Q(z)[e]/(e**(N+1)) and explicitly labelled finite illustrations.
Requires Python 3.10+ and SymPy.  No network access or floating point is used.
"""
from __future__ import annotations
from dataclasses import dataclass
from math import factorial
import sys
import sympy as s

z, e, c = s.symbols('z e c')
N = 7
checks = 0


def canon(x: s.Expr) -> s.Expr:
    return s.expand(x)


@dataclass(frozen=True)
class Jet:
    a: tuple[s.Expr, ...]

    @classmethod
    def of(cls, terms: dict[int, s.Expr] | None = None) -> 'Jet':
        terms = terms or {}
        if any(k < 0 or k > N for k in terms):
            raise ValueError('Jet exponent outside truncation range')
        return cls(tuple(s.sympify(terms.get(k, 0)) for k in range(N + 1)))

    def __add__(self, other: 'Jet') -> 'Jet':
        return Jet(tuple(canon(x+y) for x, y in zip(self.a, other.a)))

    def __neg__(self) -> 'Jet':
        return self.scale(-1)

    def __sub__(self, other: 'Jet') -> 'Jet':
        return self + (-other)

    def scale(self, q: s.Expr) -> 'Jet':
        return Jet(tuple(canon(q*x) for x in self.a))

    def __mul__(self, other: 'Jet') -> 'Jet':
        return Jet(tuple(canon(sum(self.a[j]*other.a[k-j]
                                   for j in range(k+1))) for k in range(N+1)))

    def derivative(self, order: int = 1) -> 'Jet':
        return Jet(tuple(s.diff(x, z, order) for x in self.a))

    def inverse(self) -> 'Jet':
        if self.a[0] == 0:
            raise ValueError('Inverse requires a nonzero constant coefficient')
        b = [s.cancel(1/self.a[0])]
        for n in range(1, N+1):
            b.append(s.cancel(-sum(self.a[k]*b[n-k] for k in range(1,n+1))
                              /self.a[0]))
        return Jet(tuple(b))

    def divide_e(self) -> 'Jet':
        if self.a[0] != 0:
            raise ValueError('Series is not divisible by e')
        # The new top coefficient is unknown, and is set to zero.
        # All checks involving it explicitly stop at degree N-1.
        return Jet(self.a[1:] + (s.S.Zero,))

    def expr(self) -> s.Expr:
        return sum(x*e**k for k,x in enumerate(self.a))


ZERO, ONE, Z = Jet.of(), Jet.of({0:1}), Jet.of({0:z})


def compose(g: Jet, f: Jet) -> Jet:
    """g(f(z)), for f(z)=z+O(e), truncated at degree N."""
    h = f-Z
    if h.a[0] != 0:
        raise ValueError('Substitution must reduce to the identity')
    out, power = ZERO, ONE
    for k in range(N+1):
        out = out + (power*g.derivative(k)).scale(s.Rational(1, factorial(k)))
        power = power*h
    return out


def log_vector(f: Jet) -> Jet:
    """(log T_f)(z), using powers of the finite difference operator."""
    out, term = ZERO, Z
    for k in range(1, N+1):
        term = compose(term, f)-term
        out = out+term.scale(s.Rational((-1)**(k+1), k))
    return out


def exp_apply(w: Jet, g: Jet, time: s.Expr = s.S.One) -> Jet:
    if w.a[0] != 0:
        raise ValueError('Vector field must have positive e-order')
    out, term = g, g
    for k in range(1, N+1):
        term = w*term.derivative()
        out = out+term.scale(time**k/s.factorial(k))
    return out


def log_apply(f: Jet, g: Jet) -> Jet:
    out, term = ZERO, g
    for k in range(1, N+1):
        term = compose(term, f)-term
        out = out+term.scale(s.Rational((-1)**(k+1), k))
    return out


def bernoulli_apply(w: Jet, g: Jet) -> Jet:
    out, term = g, g
    for k in range(1, N+1):
        term = w*term.derivative()
        out = out+term.scale(s.bernoulli(k,0)/s.factorial(k))
    return out


def check_expr(name: str, actual: s.Expr, expected: s.Expr = s.S.Zero) -> None:
    global checks
    if s.cancel(actual-expected) != 0:
        raise AssertionError(f'{name}: {s.cancel(actual-expected)}')
    checks += 1


def check_jet(name: str, actual: Jet, expected: Jet, through: int = N) -> None:
    for k in range(through+1):
        check_expr(f'{name}, degree {k}', actual.a[k], expected.a[k])


def main() -> None:
    print('Surcomplex dynamics: exact finite-jet verification')
    print(f'Python {sys.version.split()[0]}; SymPy {s.__version__}; N={N}')
    print('Arithmetic: exact rational functions; no numerical tolerances.\n')

    for p in range(1,4):
        f = Z+Jet.of({1:z**(p+1)})
        w = log_vector(f)
        check_jet(f'Euler p={p}: exp(log f)', exp_apply(w,Z), f)
        check_jet(f'Euler p={p}: Julia equation', compose(w,f), f.derivative()*w)
        fi = exp_apply(w,Z,-1)
        check_jet(f'Euler p={p}: inverse', compose(f,fi), Z)
        for k in range(1,N+1):
            ck = s.cancel(w.a[k]/z**(k*p+1))
            check_expr(f'Euler p={p}: grading {k}', s.diff(ck,z))
        # 1/W=e^(-1)*(W/e)^(-1); reliable through e^(N-2).
        omega = w.divide_e().inverse()
        for k in range(N):
            residue = s.residue(omega.a[k], z, 0)
            check_expr(f'Euler p={p}: residue {k}', residue,
                       s.Rational(p+1,2) if k == 1 else s.S.Zero)
        print(f'p={p}: log/exp, inverse, Julia identity, grading, and residues pass.')
        if p == 1:
            for k in range(1,7):
                print(f'  [e^{k}] W = {w.a[k]}')

    f = Z+Jet.of({1:z*z+1,2:z**3,3:z})
    w = log_vector(f)
    check_jet('mixed map round trip', exp_apply(w,Z), f)
    g, q = Jet.of({0:z**3,1:z**2}), Jet.of({0:z**2+2,2:z})
    check_jet('log equals vector derivation', log_apply(f,g), w*g.derivative())
    check_jet('log Leibniz', log_apply(f,g*q), log_apply(f,g)*q+g*log_apply(f,q))
    psi = bernoulli_apply(w,g)
    check_jet('difference equation', compose(psi,f)-psi, w*g.derivative())
    check_jet('flow group law', compose(exp_apply(w,Z,2),exp_apply(w,Z,3)),
              exp_apply(w,Z,5))
    check_jet('unique-root formula (square)',
              compose(exp_apply(w,Z,s.Rational(1,2)),
                      exp_apply(w,Z,s.Rational(1,2))), f)
    print('\nMixed-map logarithm, Leibniz, Bernoulli solver, and flow identities pass.')

    h = Z+Jet.of({1:z*z-1})
    hi = exp_apply(log_vector(h),Z,-1)
    f1 = Z+Jet.of({1:1})
    f2 = compose(h,compose(f1,hi))
    check_jet('conjugacy', compose(h,f1), compose(f2,h))
    w2 = log_vector(f2)
    check_jet('pushforward of vector field', compose(w2,h),
              h.derivative()*Jet.of({1:1}))
    b2 = w2.divide_e().inverse()
    check_jet('pullback of normalized time form', compose(b2,h)*h.derivative(),
              ONE, through=N-1)
    for k in range(1,N+1):
        check_expr('conjugator fixes basepoint 1', h.a[k].subs(z,1))
    print('Conjugacy, vector-field pushforward, time-form pullback, and marking pass.')

    # Exact, untruncated rational identities for the beyond-all-orders family.
    wc = e/(1+e*c/z)
    check_expr('flat family exact time form', 1/wc, 1/e+c/z)
    check_expr('flat family exact residue', s.residue(1/wc,z,0), c)
    check_expr('flat family leading displacement correction',
               s.limit((wc-e)/(e**2*c),c,0), -1/z)
    delta, eta = (0,1), (1,0)
    for n in range(1,51):
        check_expr(f'lexicographic illustration {n}',
                   s.Integer(eta > (n*delta[0], n*delta[1])), s.S.One)
    print('Exact rational flat-family identities pass.')
    print('Rank-two order checked for n=1,...,50 (illustration, not the all-n proof).')
    print(f'\nPASS: {checks} exact assertions.')
    print('These are finite algebraic checks, not a formal verification of the theorems.')


if __name__ == '__main__':
    main()
