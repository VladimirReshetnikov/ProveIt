#!/usr/bin/env python3
"""Exact verification for the Apéry lattice acceleration article.

Only Python's standard library is required.  The proof in the article is
symbolic and valid for all indices; these finite tests check implementation,
indexing, signs, and the resulting rational identities independently.
"""
from __future__ import annotations

import argparse
import csv
import json
import math
from decimal import Decimal, localcontext
from fractions import Fraction
from functools import lru_cache
from pathlib import Path


def nonnegative(*values: int) -> None:
    if any(not isinstance(value, int) or value < 0 for value in values):
        raise ValueError("Indices must be nonnegative integers.")


@lru_cache(maxsize=None)
def legendre_coefficient(m: int, j: int) -> int:
    nonnegative(m, j)
    return 0 if j > m else math.comb(m, j) * math.comb(m + j, j)


@lru_cache(maxsize=None)
def T(m: int, n: int) -> int:
    """OEIS A143007 as a square array (not antidiagonal indexing)."""
    nonnegative(m, n)
    return sum(legendre_coefficient(m, j) * legendre_coefficient(n, j)
               for j in range(min(m, n) + 1))


@lru_cache(maxsize=None)
def C(m: int, n: int) -> int:
    """OEIS A108625, with dimension parameter m and radius n."""
    nonnegative(m, n)
    return sum(legendre_coefficient(m, j) * math.comb(n, j)
               for j in range(min(m, n) + 1))


def harmonic(n: int, power: int) -> Fraction:
    return sum((Fraction(1, j ** power) for j in range(1, n + 1)), Fraction())


def alternating_harmonic(n: int) -> Fraction:
    return sum((Fraction(2 * (-1) ** (j + 1), j*j)
                for j in range(1, n + 1)), Fraction())


def h3(m: int, n: int) -> Fraction:
    if m < 1:
        raise ValueError("Horizontal edges require m >= 1.")
    return Fraction(1, m**3 * T(m - 1, n) * T(m, n))


def v3(m: int, n: int) -> Fraction:
    if n < 1:
        raise ValueError("Vertical edges require n >= 1.")
    return Fraction(1, n**3 * T(m, n - 1) * T(m, n))


def h2(m: int, n: int) -> Fraction:
    if m < 1:
        raise ValueError("Horizontal edges require m >= 1.")
    return Fraction(2 * (-1)**(m + 1), m*m * C(m - 1, n) * C(m, n))


def v2(m: int, n: int) -> Fraction:
    if n < 1:
        raise ValueError("Vertical edges require n >= 1.")
    return Fraction((-1)**m, n*n * C(m, n - 1) * C(m, n))


def potential3(m: int, n: int) -> Fraction:
    return harmonic(n, 3) + sum((h3(i, n) for i in range(1, m + 1)), Fraction())


def potential2(m: int, n: int) -> Fraction:
    return harmonic(n, 2) + sum((h2(i, n) for i in range(1, m + 1)), Fraction())


def term3(m: int, n: int) -> Fraction:
    return Fraction((m+n)*(m*m + m*n + n*n),
                    m**3 * n**3 * T(m-1, n-1) * T(m, n))


def term2(m: int, n: int) -> Fraction:
    return Fraction((-1)**(m+1) * (n*n + (m+n)**2),
                    m*m * n*n * C(m-1, n-1) * C(m, n))


def partial3(length: int, offset: int) -> Fraction:
    return harmonic(offset, 3) + sum(
        (term3(j, j+offset) for j in range(1, length+1)), Fraction())


def partial2_upper(length: int, offset: int) -> Fraction:
    return harmonic(offset, 2) + sum(
        (term2(j, j+offset) for j in range(1, length+1)), Fraction())


def partial2_lower(length: int, offset: int) -> Fraction:
    return alternating_harmonic(offset) + sum(
        (term2(j+offset, j) for j in range(1, length+1)), Fraction())


def error3(m: int, n: int) -> Fraction:
    """Proven positive upper bound for zeta(3) - potential3(m,n)."""
    bounds = []
    if m:
        bounds.append(Fraction(1, 2*m*m*T(m, n)*T(m+1, n)))
    if n:
        bounds.append(Fraction(1, 2*n*n*T(m, n)*T(m, n+1)))
    if not bounds:
        return Fraction(3, 2)  # zeta(3) < 1 + integral_1^infty t^-3 dt
    return min(bounds)


def error2(m: int, n: int) -> Fraction:
    """Proven bound; the signed error has sign (-1)^m."""
    bounds = [Fraction(2, (m+1)**2 * C(m, n) * C(m+1, n))]
    if n:
        bounds.append(Fraction(1, n*C(m, n)*C(m, n+1)))
    return min(bounds)


def decimal(value: Fraction, digits: int = 80) -> Decimal:
    with localcontext() as ctx:
        ctx.prec = digits
        return Decimal(value.numerator) / Decimal(value.denominator)


def certified_exponent(bound: Fraction) -> int:
    """Largest d>=0 with bound <= 10^-d, or -1 if bound>1."""
    if bound > 1:
        return -1
    d = 0
    while bound.numerator * 10 ** (d+1) <= bound.denominator:
        d += 1
    return d


def verify(max_index: int, offsets: int) -> dict[str, object]:
    counts: dict[str, int] = {}
    checks = 0
    for m in range(1, max_index+1):
        for n in range(1, max_index+1):
            a,b,c,d = T(m-1,n-1), T(m,n-1), T(m-1,n), T(m,n)
            s=(m+n)*(m*m+m*n+n*n)
            assert m**3*d+n**3*a == s*c
            assert n**3*d+m**3*a == s*b
            a,b,c,d = C(m-1,n-1), C(m,n-1), C(m-1,n), C(m,n)
            q=n*n+(m+n)**2
            assert 2*n*n*d-m*m*a == q*b
            assert m*m*d+2*n*n*a == q*c
            assert h3(m,n-1)+v3(m,n) == v3(m-1,n)+h3(m,n)
            assert h2(m,n-1)+v2(m,n) == v2(m-1,n)+h2(m,n)
            assert h3(m,n-1)+v3(m,n) == term3(m,n)
            assert h2(m,n-1)+v2(m,n) == term2(m,n)
            checks += 8
    counts['cell_and_edge_equalities'] = checks

    for m in range(max_index+1):
        for n in range(max_index+1):
            assert T(m,n) == T(n,m)
            assert potential3(m,n) == harmonic(m,3)+sum(
                (v3(m,j) for j in range(1,n+1)), Fraction())
            assert potential2(m,n) == alternating_harmonic(m)+sum(
                (v2(m,j) for j in range(1,n+1)), Fraction())
            # Independent coefficient formula from the OEIS row g.f.
            independent_c = sum(math.comb(m,j)**2*math.comb(m+n-j,m)
                                for j in range(min(m,n)+1))
            assert C(m,n) == independent_c
            # Alternative finite binomial sum listed for A143007.
            independent_t = sum(math.comb(m,j)**2*math.comb(m+n-j,m)**2
                                for j in range(min(m,n)+1))
            assert T(m,n) == independent_t
    counts['potential_symmetry_and_independent_array_checks'] = 5*(max_index+1)**2

    for k in range(offsets+1):
        for length in range(max_index+1):
            assert partial3(length,k) == potential3(length,length+k)
            assert partial2_upper(length,k) == potential2(length,length+k)
            assert partial2_lower(length,k) == potential2(length+k,length)
    counts['finite_diagonal_equalities'] = 3*(offsets+1)*(max_index+1)

    for n in range(1,max_index):
        a0,a1,a2=T(n-1,n-1),T(n,n),T(n+1,n+1)
        b0,b1,b2=C(n-1,n-1),C(n,n),C(n+1,n+1)
        assert (n+1)**3*a2 == (34*n**3+51*n*n+27*n+5)*a1-n**3*a0
        assert (n+1)**2*b2 == (11*n*n+11*n+3)*b1+n*n*b0
        p0,p1,p2=(T(j,j)*potential3(j,j) for j in [n-1,n,n+1])
        r0,r1,r2=(C(j,j)*potential2(j,j) for j in [n-1,n,n+1])
        assert (n+1)**3*p2 == (34*n**3+51*n*n+27*n+5)*p1-n**3*p0
        assert (n+1)**2*r2 == (11*n*n+11*n+3)*r1+n*n*r0
    counts['diagonal_recurrence_equalities'] = 4*max(0,max_index-1)

    assert [T(j,j) for j in range(7)] == [1,5,73,1445,33001,819005,21460825]
    assert [C(j,j) for j in range(7)] == [1,3,19,147,1251,11253,104959]
    counts['source_prefix_checks'] = 2
    return {'status':'PASS', 'max_index':max_index, 'max_offset':offsets,
            'checks':counts, 'total_equalities':sum(counts.values()),
            'arithmetic':'exact Python integers and fractions.Fraction',
            'warning':'Finite computations check implementation, not universal validity.'}


def write_artifacts(folder: Path) -> None:
    folder.mkdir(parents=True, exist_ok=True)
    with (folder/'array_prefixes.csv').open('w', newline='') as stream:
        writer=csv.writer(stream)
        writer.writerow(['m','n','T_A143007','C_A108625'])
        for m in range(13):
            for n in range(13):
                writer.writerow([m,n,T(m,n),C(m,n)])
    with (folder/'certified_intervals.csv').open('w', newline='') as stream:
        writer=csv.writer(stream)
        writer.writerow(['family','offset','terms','partial_numerator','partial_denominator',
                         'bound_numerator','bound_denominator','error_sign',
                         'certified_absolute_error_exponent','partial_decimal','bound_decimal'])
        for name, partial, error, orient in [
            ('zeta3',partial3,error3,'upper'),
            ('zeta2_upper',partial2_upper,error2,'upper'),
            ('zeta2_lower',partial2_lower,error2,'lower')]:
            for k in [0,1,3]:
                for length in [5,10,20,40]:
                    m,n=(length,length+k) if orient=='upper' else (length+k,length)
                    value=partial(length,k)
                    bound=error(m,n)
                    sign=1 if name=='zeta3' else (-1)**m
                    writer.writerow([name,k,length,value.numerator,value.denominator,
                                     bound.numerator,bound.denominator,sign,
                                     certified_exponent(bound),str(decimal(value,145)),
                                     f'{decimal(bound,12):.6E}'])
    with (folder/'sample_partial_sums.txt').open('w') as stream:
        for family,fun in [('zeta3',partial3),('zeta2_upper',partial2_upper),
                           ('zeta2_lower',partial2_lower)]:
            for k in range(3):
                stream.write(f'{family}, offset={k}\n')
                for length in range(1,5):
                    stream.write(f'  N={length}: {fun(length,k)}\n')


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-index',type=int,default=40)
    parser.add_argument('--offsets',type=int,default=12)
    parser.add_argument('--output-dir',type=Path,default=Path('data'))
    args=parser.parse_args()
    if args.max_index<6 or args.offsets<0:
        parser.error('--max-index must be >=6 and --offsets must be >=0')
    result=verify(args.max_index,args.offsets)
    write_artifacts(args.output_dir)
    result_path=args.output_dir/'verification_results.json'
    result_path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
