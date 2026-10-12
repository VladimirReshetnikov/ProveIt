"""Exact coefficient and rationality utilities for the accompanying article.

All coefficients returned by gamma_coefficients are ordinary Taylor
coefficients, NOT derivatives. Symbol Zr represents zeta(r); L is log(2).
Only finite exact arithmetic is used in the symbolic routines.
"""
from __future__ import annotations
from collections import Counter, defaultdict
from fractions import Fraction
from math import floor
import sympy as sp

L, T = sp.symbols('L T')

def Z(r: int) -> sp.Symbol:
    if r < 2:
        raise ValueError('Zeta index must be at least 2.')
    return sp.Symbol(f'Z{r}')

def trunc_t(expr: sp.Expr, degree: int) -> sp.Expr:
    p = sp.Poly(sp.expand(expr), T)
    return sp.Add(*(coef*T**mon[0] for mon, coef in p.terms()
                    if mon[0] <= degree))

def gamma_coefficients(max_u: int, max_t2: int) -> list[sp.Expr]:
    """Return [u^r] G(u,t), with T=t^2, truncated to T^max_t2."""
    if max_u < 0 or max_t2 < 0:
        raise ValueError('Truncation orders must be nonnegative.')
    logs: list[sp.Expr] = [sp.Integer(0)]
    for r in range(1, max_u + 1):
        base = 4*L if r == 1 else sp.Rational(2*(-1)**r*(2-2**r), r)*Z(r)
        mixed = sp.Add(*(sp.Rational(2*(-1)**(r+1), r)
                    * sp.binomial(r+2*k-1, 2*k)
                    * (sp.Integer(2)**r-sp.Rational(1, 2**(2*k)))
                    * Z(r+2*k)*T**k for k in range(1, max_t2+1)))
        logs.append(base+mixed)
    out: list[sp.Expr] = [sp.Integer(1)]
    for n in range(1, max_u+1):
        out.append(trunc_t(sum(r*logs[r]*out[n-r]
                               for r in range(1, n+1))/n, max_t2))
    return out

def harmonic_sum_coefficient(m: int, k: int,
                             coefficients: list[sp.Expr] | None = None) -> sp.Expr:
    """Sum C_m(n)/(2n+1)^(2k+1), in the formal zeta/log algebra."""
    if m < 0 or k < 1:
        raise ValueError('Require m>=0, k>=1.')
    co = coefficients if coefficients is not None else gamma_coefficients(m+1,k)
    return sp.expand(sp.Rational((-1)**m,4)*co[m+1].coeff(T,k))

def reduce_even_zetas(expr: sp.Expr) -> sp.Expr:
    replacement = {}
    for symbol in expr.free_symbols:
        name = str(symbol)
        if name.startswith('Z') and name[1:].isdigit():
            r = int(name[1:])
            if r > 2 and r % 2 == 0:
                j = r//2
                replacement[symbol] = ((-1)**(j+1)*sp.bernoulli(2*j)
                    * 2**(2*j)*6**j/(2*sp.factorial(2*j))*Z(2)**j)
    return sp.expand(expr.subs(replacement))

def rational_divisor(shifts: list[Fraction]) -> dict[Fraction,int] | None:
    """Divisor of x*prod Gamma(x+a)/Gamma(x+1-a), or None if nonrational.

    Keys s represent factors (x+s). Pairing is performed solely through
    residue classes mod Z, independently of the classification theorem.
    """
    top = defaultdict(list); bottom = defaultdict(list)
    for a in shifts:
        top[a-floor(a)].append(a)
        b = 1-a
        bottom[b-floor(b)].append(b)
    if set(top) != set(bottom) or any(len(top[r]) != len(bottom[r]) for r in top):
        return None
    divisor = Counter({Fraction(0):1})
    for r in top:
        for a,b in zip(sorted(top[r]),sorted(bottom[r])):
            h = a-b
            assert h.denominator == 1
            if h >= 0:
                for j in range(int(h)): divisor[b+j] += 1
            else:
                for j in range(int(-h)): divisor[a+j] -= 1
    return {s:e for s,e in divisor.items() if e}

def classify(N: int, kappa: Fraction, b: Fraction, c: Fraction) -> dict:
    """The theorem's prediction in the article's positive-parameter domain."""
    if N < 0 or min(kappa,b,c,1+2*kappa-b-c) <= 0:
        raise ValueError('Require N>=0 and kappa,b,c,d0>0.')
    d=1+2*kappa-b-c+N
    parameters=(b,c,d)
    rational=any(p.denominator==1 for p in parameters)
    polynomial=any(p.denominator==1 and 1 <= p <= N for p in parameters)
    exceptional=any(parameters[i] == N+1
                    and all(parameters[j] == kappa for j in range(3) if j!=i)
                    for i in range(3))
    return {'rational':rational,'terminates':polynomial or exceptional,
            'polynomial_locus':polynomial,'exceptional_locus':exceptional}

def compositions(m: int):
    if m == 0:
        yield ()
    else:
        for first in range(1,m+1):
            for tail in compositions(m-first):
                yield (first,)+tail

def finite_harmonic(n: int, indices: tuple[int,...]) -> sp.Rational:
    """Strictly decreasing finite harmonic sum H_n(indices)."""
    if not indices: return sp.Integer(1)
    if n < len(indices): return sp.Integer(0)
    return sum(sp.Rational(1,j**indices[0])*finite_harmonic(j-1,indices[1:])
               for j in range(1,n+1))

def composition_coefficient(n: int,m: int) -> sp.Rational:
    return sum(2**len(c)*finite_harmonic(n,c) for c in compositions(m))
