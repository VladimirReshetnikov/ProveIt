#!/usr/bin/env python3
"""Exact Catalan Hankel determinants and sharp recurrence checks.

Python 3.10+, standard library only. Coefficient arrays use ascending powers.
All matrix arithmetic is rational and uses pivoting. No floating-point tests.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from math import comb, factorial, prod
from typing import Iterable, Sequence


def pmul(a: Sequence[F | int], b: Sequence[F | int]) -> list[F]:
    """Multiply polynomials represented in ascending powers."""
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return out


def peval(a: Sequence[F | int], x: F | int) -> F:
    ans = F(0)
    for c in reversed(a):
        ans = ans*x+c
    return ans


def determinant(a: Sequence[Sequence[F | int]]) -> F:
    """Exact Gaussian determinant with row pivoting, including 0-by-0."""
    n = len(a)
    if any(len(row) != n for row in a):
        raise ValueError('matrix must be square')
    b = [[F(x) for x in row] for row in a]
    ans = F(1)
    for k in range(n):
        pivot = next((r for r in range(k, n) if b[r][k]), None)
        if pivot is None:
            return F(0)
        if pivot != k:
            b[k], b[pivot] = b[pivot], b[k]
            ans = -ans
        v = b[k][k]
        ans *= v
        for r in range(k+1, n):
            if b[r][k]:
                f = b[r][k]/v
                for j in range(k+1, n):
                    b[r][j] -= f*b[k][j]
                b[r][k] = F(0)
    return ans


def solve(a: Sequence[Sequence[F | int]], b: Sequence[F | int]) -> list[F] | None:
    """Solve a possibly overdetermined rational system; free variables are zero."""
    if len(a) != len(b):
        raise ValueError('row counts differ')
    n = len(a[0]) if a else 0
    if any(len(row) != n for row in a):
        raise ValueError('ragged matrix')
    m = [[F(x) for x in row] + [F(y)] for row, y in zip(a, b)]
    pivots: list[int] = []
    r = 0
    for c in range(n):
        p = next((i for i in range(r, len(m)) if m[i][c]), None)
        if p is None:
            continue
        m[r], m[p] = m[p], m[r]
        v = m[r][c]
        m[r] = [x/v for x in m[r]]
        for i in range(len(m)):
            if i != r and m[i][c]:
                v = m[i][c]
                m[i] = [x-v*y for x,y in zip(m[i],m[r])]
        pivots.append(c)
        r += 1
        if r == len(m):
            break
    if any(not any(row[:n]) and row[n] for row in m):
        return None
    ans = [F(0)]*n
    for i,c in enumerate(pivots):
        ans[c] = m[i][n]
    return ans


def catalan(n: int) -> int:
    if n < 0:
        raise ValueError('Catalan index must be nonnegative')
    return comb(2*n,n)//(n+1)


def direct_hankel(n: int, coefficients: Sequence[F | int]) -> F:
    """Determinant from its original moment matrix, not the Christoffel formula."""
    if n < 0 or not coefficients:
        raise ValueError('nonnegative size and nonempty coefficient list required')
    moments = [sum(F(c)*catalan(i+k) for k,c in enumerate(coefficients))
               for i in range(max(0,2*n-1))]
    return determinant([[moments[i+j] for j in range(n)] for i in range(n)])


@dataclass(frozen=True)
class Root:
    value: F
    multiplicity: int

    def __post_init__(self) -> None:
        object.__setattr__(self, 'value', F(self.value))
        if self.multiplicity < 1:
            raise ValueError('multiplicity must be positive')


def multiplier(roots: Sequence[Root], leading: F | int = 1) -> list[F]:
    coefficients = [F(leading)]
    for root in roots:
        for _ in range(root.multiplicity):
            coefficients = pmul(coefficients, [-root.value, F(1)])
    return coefficients


def jets(c: F | int, multiplicity: int, max_index: int) -> list[list[F]]:
    """P_n^(r)(c)/r! from the polynomial recurrence, for all required n,r."""
    if multiplicity < 1 or max_index < 0:
        raise ValueError('positive jet length and nonnegative maximum index required')
    c = F(c)
    p0 = [F(1)]+[F(0)]*(multiplicity-1)
    out = [p0]
    if max_index == 0:
        return out
    p1 = [c-1]+[F(1) if r == 1 else F(0) for r in range(1,multiplicity)]
    out.append(p1)
    for n in range(1,max_index):
        out.append([(c-2)*out[n][r] + (out[n][r-1] if r else 0)
                    -out[n-1][r] for r in range(multiplicity)])
    return out


def christoffel_values(roots: Sequence[Root], leading: F | int,
                       count: int) -> list[F]:
    """H_0,...,H_(count-1), using a fixed-size confluent determinant.

    Root values are rational in this reference implementation. The article's
    theorem allows arbitrary complex root values.
    """
    if count < 0 or not leading:
        raise ValueError('count must be nonnegative and leading coefficient nonzero')
    if len({r.value for r in roots}) != len(roots):
        raise ValueError('combine repeated root values into a single Root')
    d = sum(r.multiplicity for r in roots)
    if not roots:
        return [F(leading)**n for n in range(count)]
    delta = prod((roots[j].value-roots[i].value)**
                 (roots[i].multiplicity*roots[j].multiplicity)
                 for i in range(len(roots)) for j in range(i+1,len(roots)))
    tables = [jets(r.value,r.multiplicity,count+d) for r in roots]
    out = []
    for n in range(count):
        matrix = [[table[n+j][a] for j in range(d)]
                  for r,table in zip(roots,tables) for a in range(r.multiplicity)]
        out.append(F((-1)**(n*d))*F(leading)**n*determinant(matrix)/delta)
    return out


def sharp_order_bound(m: int, ell: int, multiplicities: Sequence[int]) -> int:
    if min(m,ell) < 0 or any(t < 1 for t in multiplicities):
        raise ValueError('invalid multiplicities')
    kappa = m*(m-1)//2+ell*(ell+1)//2
    total = prod(t+1 for t in multiplicities)*(F(kappa+1)
            +sum((F(t*(t-1),6) for t in multiplicities),F(0)))
    if total.denominator != 1:
        raise ArithmeticError('order formula must be integral')
    return total.numerator


@dataclass(frozen=True)
class Sector:
    counts: tuple[int, ...]
    rate: F
    degree: int
    leading: F


def sectors(m: int, ell: int, blocks: Sequence[tuple[F | int,int]],
            leading: F | int = 1) -> list[Sector]:
    """Rates, exact degrees and leading constants for rational spectral z_i.

    Each (z_i,t_i) encodes c_i = 2 + z_i + 1/z_i. The order of roots
    throughout is 0,4,c_1,..., with absent endpoint blocks omitted.
    """
    if min(m,ell) < 0 or not leading:
        raise ValueError('invalid endpoints or leading coefficient')
    blocks = [(F(z),t) for z,t in blocks]
    if any(z in (0,1,-1) or t < 1 for z,t in blocks):
        raise ValueError('z must avoid 0,+1,-1 and t must be positive')
    roots = ([] if not m else [Root(F(0),m)])
    roots += [] if not ell else [Root(F(4),ell)]
    roots += [Root(2+z+1/z,t) for z,t in blocks]
    if len({r.value for r in roots}) != len(roots):
        raise ValueError('distinct root values required')
    delta = prod((roots[j].value-roots[i].value)**
                 (roots[i].multiplicity*roots[j].multiplicity)
                 for i in range(len(roots)) for j in range(i+1,len(roots)))
    k0 = m*(m-1)//2
    k4 = ell*(ell+1)//2
    b0 = F((-2)**k0,prod(factorial(2*r) for r in range(m)))
    b4 = F(2**k4,prod(factorial(2*r+1) for r in range(ell)))
    answer = []
    for ks in product(*(range(t+1) for z,t in blocks)):
        rate = F(leading)*(-1)**(ell+sum(t for z,t in blocks))
        degree = k0+k4
        const = b0*b4
        groups = ([] if not m else [(F(-1),m)])
        groups += [] if not ell else [(F(1),ell)]
        for (z,t),k in zip(blocks,ks):
            h = t-k
            s = 1/(z-1/z)
            ap,am = z/(z-1),-1/(z-1)
            const *= (ap**k*am**h*s**(k*(k-1)//2)*(-s)**(h*(h-1)//2)
                      *(-2*s)**(k*h)/prod(factorial(r) for r in range(t)))
            rate *= z**(2*k-t)
            degree += k*h
            if k:
                groups.append((z,k))
            if h:
                groups.append((1/z,h))
        v = F(1)
        for w,u in groups:
            v *= w**(u*(u-1)//2)*prod(factorial(h) for h in range(u))
        for i,(w,u) in enumerate(groups):
            for v2,u2 in groups[i+1:]:
                v *= (v2-w)**(u*u2)
        const *= v/delta
        answer.append(Sector(tuple(ks),rate,degree,F(const)))
    return answer


def characteristic(items: Sequence[Sector], combine_equal: bool = False) -> list[F]:
    """An annihilator; minimal for distinct rates. Ascending coefficients."""
    rates: list[tuple[F,int]]
    if combine_equal:
        table: dict[F,int] = {}
        for s in items:
            table[s.rate] = max(table.get(s.rate,0),s.degree+1)
        rates = list(table.items())
    else:
        rates = [(s.rate,s.degree+1) for s in items]
    p = [F(1)]
    for rate,e in rates:
        for _ in range(e):
            p = pmul(p,[-rate,F(1)])
    return p


def secondary_hankel_formula(items: Sequence[Sector]) -> F:
    """Exact determinant of (H_(i+j)) at the full labelled-sector order.

    The product remains valid at resonances, when it vanishes.
    """
    out = F(1)
    for s in items:
        r = s.degree+1
        out *= (-1)**(r*(r-1)//2)
        out *= (factorial(s.degree)*s.leading)**r * s.rate**(r*(r-1))
    for i,s in enumerate(items):
        for t in items[i+1:]:
            out *= (t.rate-s.rate)**(2*(s.degree+1)*(t.degree+1))
    return out


def fit_sectors(values: Sequence[F | int], items: Sequence[Sector]) -> list[list[F]]:
    """Recover sector polynomials for distinct rates using exact interpolation."""
    if len({s.rate for s in items}) != len(items):
        raise ValueError('sector interpolation requires distinct rates')
    r = sum(s.degree+1 for s in items)
    if len(values) < r:
        raise ValueError('insufficient values')
    matrix = [[F(n)**j*s.rate**n for s in items for j in range(s.degree+1)]
              for n in range(r)]
    solution = solve(matrix,values[:r])
    if solution is None:
        raise ArithmeticError('singular interpolation system')
    out,offset = [],0
    for s in items:
        out.append(solution[offset:offset+s.degree+1])
        offset += s.degree+1
    return out


def minimal_recurrence(values: Sequence[F | int], bound: int) -> list[F]:
    """Recover a provably minimal recurrence GIVEN a proved order bound.

    For each r<=bound, test q(E)H=0 at bound consecutive starting indices.
    The article proves that 2*bound values suffice. The routine does not
    itself certify that an arbitrary input sequence has that order bound.
    """
    if bound < 1 or len(values) < 2*bound:
        raise ValueError('need a positive bound and at least twice that many values')
    for r in range(1,bound+1):
        a = [[values[n+j] for j in range(r)] for n in range(bound)]
        b = [-values[n+r] for n in range(bound)]
        sol = solve(a,b)
        if sol is not None:
            return sol+[F(1)]
    raise ArithmeticError('the supplied order bound is incompatible with the data')


def recurrence_residuals(values: Sequence[F | int], p: Sequence[F | int]) -> list[F]:
    return [sum(F(c)*values[n+j] for j,c in enumerate(p))
            for n in range(len(values)-len(p)+1)]


def _trim(p: Sequence[F | int]) -> list[F]:
    out = [F(v) for v in p]
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out or [F(0)]


def _pdivmod(a: Sequence[F | int], b: Sequence[F | int]) -> tuple[list[F],list[F]]:
    a,b = _trim(a),_trim(b)
    if b == [0]:
        raise ZeroDivisionError('zero polynomial divisor')
    q = [F(0)]*max(1,len(a)-len(b)+1)
    while a != [0] and len(a) >= len(b):
        shift = len(a)-len(b)
        v = a[-1]/b[-1]
        q[shift] += v
        for j,c in enumerate(b):
            a[j+shift] -= v*c
        a = _trim(a)
    return _trim(q),a


def _pquot(a: Sequence[F | int], b: Sequence[F | int]) -> list[F]:
    q,r = _pdivmod(a,b)
    if r != [0]:
        raise ArithmeticError('polynomial division was not exact')
    return q


def _pgcd(a: Sequence[F | int], b: Sequence[F | int]) -> list[F]:
    a,b = _trim(a),_trim(b)
    while b != [0]:
        a,b = b,_pdivmod(a,b)[1]
    return [v/a[-1] for v in a] if a != [0] else a


def multiplicity_profile(coefficients: Sequence[F | int]) -> tuple[int,int,dict[int,int]]:
    """Return multiplicities at 0,4 and counts d_t of other roots of multiplicity t.

    Uses rational polynomial gcds, not root finding or irreducible factorization.
    Counts include all complex roots, not only real roots.
    """
    f = _trim(coefficients)
    if f == [0]:
        raise ValueError('the zero polynomial is excluded')
    f = [v/f[-1] for v in f]
    m = ell = 0
    while len(f) > 1 and f[0] == 0:
        f = f[1:]; m += 1
    while len(f) > 1 and peval(f,4) == 0:
        f = _pquot(f,[-4,1]); ell += 1
    derivative = [j*f[j] for j in range(1,len(f))] or [F(0)]
    c = _pgcd(f,derivative)
    w = _pquot(f,c)
    counts: dict[int,int] = {}
    t = 1
    while len(w) > 1:
        y = _pgcd(w,c)
        z = _pquot(w,y)
        if len(z) > 1:
            counts[t] = len(z)-1
        w = y
        c = _pquot(c,y)
        t += 1
    return m,ell,counts


def recurrence_from_coefficients(coefficients: Sequence[F | int],
                                 max_bound: int | None = None) -> tuple[list[F],int]:
    """Exact minimal recurrence for any nonzero rational polynomial multiplier.

    Returns (ascending monic characteristic polynomial, proved order bound).
    This transparent fallback computes original determinants through size
    2*bound-1. It is intentionally not a high-performance implementation.
    max_bound optionally refuses unexpectedly expensive calculations.
    """
    m,ell,counts = multiplicity_profile(coefficients)
    ts = [t for t,d in counts.items() for _ in range(d)]
    bound = sharp_order_bound(m,ell,ts)
    if max_bound is not None and bound > max_bound:
        raise ValueError(f'proved bound {bound} exceeds max_bound {max_bound}')
    values = [direct_hankel(n,coefficients) for n in range(2*bound)]
    return minimal_recurrence(values,bound),bound


if __name__ == '__main__':
    roots = [Root(F(9,2),4)]
    vals = christoffel_values(roots,16,12)
    print('Multiplier: (2*x-9)^4')
    print('H_0,...,H_11:', ', '.join(str(v) for v in vals))
    print('Sharp recurrence order:', sharp_order_bound(0,0,[4]))
