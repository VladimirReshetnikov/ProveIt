#!/usr/bin/env python3
"""Exact checks for fixed-sector LIS holonomicity and asymptotic coefficients.

Run: python verify.py --output results
Standard-library tests are exact. SymPy and mpmath add symbolic/numerical tests.
The tests supplement, not replace, the mathematical proof in article.pdf.
No network access or input files are needed.
"""
from __future__ import annotations
import argparse
import csv
import json
import math
from fractions import Fraction
from functools import lru_cache
from itertools import permutations
from pathlib import Path
from time import perf_counter
from typing import Iterator


def partitions(n: int, cap: int | None = None) -> Iterator[tuple[int, ...]]:
    if n < 0:
        return
    if n == 0:
        yield ()
        return
    if cap is None:
        cap = n
    for first in range(min(cap, n), 0, -1):
        for tail in partitions(n-first, first):
            yield (first,) + tail


def dimension(lam: tuple[int, ...]) -> int:
    """Hook-length formula, with an exact divisibility assertion."""
    hook_product = 1
    for i, row in enumerate(lam):
        for col in range(1, row+1):
            below = sum(other >= col for other in lam[i+1:])
            hook_product *= row-col+below+1
    q, rem = divmod(math.factorial(sum(lam)), hook_product)
    assert rem == 0
    return q


@lru_cache(maxsize=None)
def shape_data(n: int) -> tuple[tuple[tuple[int, ...], int], ...]:
    return tuple((lam, dimension(lam)**2) for lam in partitions(n))


def counts(n: int, k: int, max_j: int = 4) -> tuple[int, int, tuple[int, ...]]:
    exact = tail = 0
    moments = [0] * max_j
    for lam, weight in shape_data(n):
        first = lam[0] if lam else 0
        exact += weight * (first == k)
        tail += weight * (first >= k)
        # One-based row i: lambda_i - i >= k-1.
        y = sum(row - i >= k-1 for i, row in enumerate(lam, 1))
        for j in range(1, min(y, max_j)+1):
            moments[j-1] += weight * math.comb(y, j)
    return exact, tail, tuple(moments)


def first_moment(n: int, k: int) -> int:
    if n < 0 or k < 1:
        raise ValueError('Require n >= 0 and k >= 1.')
    value = math.factorial(n)**2 * sum(
        (Fraction((-1)**(m-k)*math.comb(2*m-2, m-k),
                  math.factorial(m)**2*math.factorial(n-m))
         for m in range(k, n+1)), Fraction())
    assert value.denominator == 1
    return value.numerator


def a269021(n: int) -> int:
    if n < 0:
        raise ValueError('Require n >= 0.')
    return 1 if n == 0 else first_moment(2*n, n)


def poly_mul(a: list[Fraction], b: list[Fraction], deg: int) -> list[Fraction]:
    c = [Fraction(0)]*(deg+1)
    for i, x in enumerate(a[:deg+1]):
        if not x:
            continue
        for j, y in enumerate(b[:deg+1-i]):
            if y:
                c[i+j] += x*y
    return c


def increasing_tuples(j: int, budget: int, start: int = 0) -> Iterator[tuple[int, ...]]:
    if j == 0:
        yield ()
        return
    # x+(x+1)+...+(x+j-1) <= budget.
    largest = (budget-j*(j-1)//2)//j
    for x in range(start, largest+1):
        for rest in increasing_tuples(j-1, budget-x, x+1):
            yield (x,)+rest


def permutation_sign(p: tuple[int, ...]) -> int:
    return (-1)**sum(p[a] > p[b] for a in range(len(p)) for b in range(a+1, len(p)))


@lru_cache(maxsize=None)
def reduced_bessel(d: int, deg: int) -> tuple[Fraction, ...]:
    # J_d(2 sqrt(t)) = t^(d/2) times this series.
    return tuple(Fraction((-1)**s, math.factorial(s)*math.factorial(d+s))
                 for s in range(deg+1))


def bessel_moment(n: int, k: int, j: int) -> int:
    """Independent finite power-series evaluation of the squared-minor formula."""
    if min(k, j) < 1 or n < 0:
        raise ValueError('Require n >= 0, k,j >= 1.')
    min_sum = j*(j-1)//2
    budget = n-j*k
    if budget < 2*min_sum:
        return 0
    total = Fraction()
    for u in increasing_tuples(j, budget-min_sum):
        for v in increasing_tuples(j, budget-sum(u)):
            base = j*k+sum(u)+sum(v)
            deg = n-base
            det = [Fraction() for _ in range(deg+1)]
            for p in permutations(range(j)):
                term = [Fraction(1)]
                for a in range(j):
                    term = poly_mul(term, list(reduced_bessel(k+u[a]+v[p[a]], deg)), deg)
                sign = permutation_sign(p)
                for d in range(deg+1):
                    det[d] += sign*term[d]
            squared = poly_mul(det, det, deg)
            total += sum((squared[d]/math.factorial(deg-d) for d in range(deg+1)), Fraction())
    total *= math.factorial(n)**2
    assert total.denominator == 1
    return total.numerator


def write_csv(path: Path, header: list[str], rows: list[list[object]]) -> None:
    with path.open('w', newline='', encoding='utf-8') as stream:
        writer = csv.writer(stream)
        writer.writerow(header)
        writer.writerows(rows)


def exact_tests(out: Path) -> dict[str, object]:
    nmax = 26
    cells = 0
    rows = []
    for n in range(nmax+1):
        assert sum(w for _, w in shape_data(n)) == math.factorial(n)
        for k in range(1, n+2):
            exact, tail, moments = counts(n, k)
            assert first_moment(n, k) == moments[0]
            for R in range(1, 5):
                trunc = sum((-1)**(j+1)*moments[j-1] for j in range(1, R+1))
                residual = sum(w*math.comb(y-1, R)
                    for lam, w in shape_data(n)
                    if (y := sum(row-i >= k-1 for i, row in enumerate(lam, 1))) >= 1)
                assert trunc-tail == (-1)**(R+1)*residual
                if n < (R+1)*(k+R):
                    assert trunc == tail
                    next_moments = counts(n, k+1)[2]
                    next_trunc = sum((-1)**(j+1)*next_moments[j-1]
                                     for j in range(1, R+1))
                    assert trunc-next_trunc == exact
                if n == (R+1)*(k+R):
                    rectangle = (k+R,)*(R+1)
                    assert trunc-tail == (-1)**(R+1)*dimension(rectangle)**2
            if n <= 15:
                rows.append([n, k, exact, tail, *moments])
            cells += 1
    write_csv(out/'small_counts.csv', ['N','k','exact_LIS','tail_LIS','C1','C2','C3','C4'], rows)

    bessel_rows = []
    # Include nonzero j=3 contributions, not only empty supports.
    for j, kmax, nmax_b in [(1,4,12),(2,4,14),(3,2,13)]:
        for k in range(1, kmax+1):
            for n in range(nmax_b+1):
                value = bessel_moment(n,k,j)
                assert value == counts(n,k,max_j=j)[2][j-1]
                bessel_rows.append([n,k,j,value])
    write_csv(out/'bessel_checks.csv', ['N','k','j','Cj'], bessel_rows)

    # Independent published OEIS display, 0..15 (retrieved 2026-10-03).
    reference = [1,2,23,588,24553,1438112,108469917,9996042284,
        1086997811325,136102249609224,19269396089593156,
        3042212958893941456,529708789768374664407,
        100813134967124531098768,20816198414187782633783462,
        4634136282168760818748363080]
    point_reference = [1,1,13,381,17557,1100902,87116283,8312317976,
        927716186325,118504614869214,17044414451764396,
        2725298085020712539,479491040778079234419,
        92050364310704637832186,19146538134094625864605786,
        4289203871330156652985437480]
    point_values = [1]+[first_moment(2*n,n)-first_moment(2*n,n+1) for n in range(1,61)]
    assert point_values[:len(point_reference)] == point_reference
    write_csv(out/'a267433.csv',['n','b_n'],list(map(list,enumerate(point_values))))
    values = [a269021(n) for n in range(61)]
    assert values[:len(reference)] == reference
    write_csv(out/'a269021.csv',['n','a_n'],list(map(list,enumerate(values))))
    return {'partition_sizes_checked': [0,nmax], 'cells_checked': cells,
            'truncation_ranks_checked': [1,4], 'bessel_comparisons':len(bessel_rows),
            'oeis_terms_matched':len(reference), 'a267433_oeis_terms_matched':len(point_reference), 'a269021_terms_generated':len(values)}


def symbolic_tests(out: Path) -> dict[str, object]:
    import sympy as sp
    from sympy.functions.combinatorial.numbers import stirling
    j,r,rho,u = sp.symbols('j r rho u')
    order = 5
    logs = []
    polys = [sp.Integer(1)]
    coefficients = []
    for ell in range(1,order+1):
        log = sp.expand(sp.Rational((-1)**(ell+1),ell)*(
            sp.summation(((2*j-2-r)/2)**ell,(r,0,j-1))
            + sp.summation((-r/rho)**ell,(r,0,j-1))
            - 2*sp.summation(r**ell,(r,1,j))))
        logs.append(log)
        polys.append(sp.expand(sum(a*logs[a-1]*polys[ell-a]
                                   for a in range(1,ell+1))/ell))
    for p in polys:
        c = sum(coeff*sum(stirling(deg[0],b,kind=2)*(-2*rho)**b
                         for b in range(deg[0]+1))
                for deg,coeff in sp.Poly(p,j).terms())
        coefficients.append(sp.factor(c))
    assert sp.expand(coefficients[1]-(2*rho-rho**2)) == 0
    assert [c.subs(rho,1) for c in coefficients] == [1,1,sp.Rational(9,2),7,
                                                    -sp.Rational(149,8),-sp.Rational(3911,40)]
    log_central = sum(2*sp.bernoulli(2*ell)/(2*ell*(2*ell-1))
                     *(sp.Rational(1,2)**(2*ell-1)-2)*u**(2*ell-1)
                     for ell in range(1,4))
    central = sp.series(sp.exp(log_central),u,0,order+1).removeO()
    correction = sp.series(central*sum(c.subs(rho,1)*u**i
                                     for i,c in enumerate(coefficients)),u,0,order+1).removeO()
    diagonal = [sp.expand(correction).coeff(u,i) for i in range(order+1)]
    assert diagonal == [1,sp.Rational(3,4),sp.Rational(137,32),sp.Rational(757,128),
                        -sp.Rational(41429,2048),-sp.Rational(3803959,40960)]
    # Independent finite-j product expansion at several rho,j pairs.
    for rv in [sp.Rational(1,2),sp.Integer(1),sp.Integer(2)]:
        for jj in [0,1,2,4,7]:
            q = [Fraction(1)]+[Fraction(0)]*order
            rr = Fraction(int(rv.p), int(rv.q))
            for rvalue in range(jj):
                q = poly_mul(q, [Fraction(1), Fraction(2*jj-2-rvalue,2)], order)
                q = poly_mul(q, [Fraction(1), -Fraction(rvalue)/rr], order)
            for rvalue in range(1,jj+1):
                q = poly_mul(q, [Fraction((-1)**d*(d+1)*rvalue**d)
                                 for d in range(order+1)], order)
            for i,p in enumerate(polys):
                assert sp.Rational(q[i].numerator,q[i].denominator) == sp.expand(p.subs({j:jj,rho:rv}))
    next_rho = (rho-u)/(1+u)
    next_exp = sp.series(sp.exp(2*(rho-next_rho)),u,0,4).removeO()
    next_coeffs = sum(sp.series(coefficients[d].subs(rho,next_rho)*(u/(1+u))**d,u,0,4).removeO()
                      for d in range(4))
    point = sp.series(sum(coefficients[d]*u**d for d in range(4))
                      -rho*u/(1+u)**2*next_exp*next_coeffs,u,0,4).removeO()
    point = [sp.factor(sp.expand(point).coeff(u,d)) for d in range(4)]
    assert sp.expand(point[1]-(rho-rho**2)) == 0
    assert sp.expand(point[2]-(rho**4/2-7*rho**3/3+3*rho**2+rho/3)) == 0
    assert sp.expand(point[3]-(-rho**6/6+11*rho**5/6-41*rho**4/6+31*rho**3/3-2*rho**2/3-2*rho)) == 0
    point_diagonal = sp.series(sum(point[d].subs(rho,1)*u**d for d in range(4))*central,u,0,4).removeO()
    assert [sp.expand(point_diagonal).coeff(u,d) for d in range(4)] == [1,-sp.Rational(1,4),sp.Rational(49,32),sp.Rational(273,128)]
    data = {'c_rho':[str(c) for c in coefficients], 'point_c_rho':[str(c) for c in point],
            'c_at_one':[str(c.subs(rho,1)) for c in coefficients],
            'a269021_corrections':[str(c) for c in diagonal]}
    (out/'symbolic_coefficients.json').write_text(json.dumps(data,indent=2)+'\n')
    (out/'coefficients.tex').write_text('\n'.join(
        f'% c_{i}(rho)\n{sp.latex(c)}' for i,c in enumerate(coefficients))+'\n')
    return {'orders_generated':order,'finite_product_crosschecks':15,**data}


def numerical_tests(out: Path) -> dict[str, object]:
    import mpmath as mp
    mp.mp.dps = 100
    d = [Fraction(1),Fraction(3,4),Fraction(137,32),Fraction(757,128),
         -Fraction(41429,2048),-Fraction(3803959,40960)]
    rows = []
    for n in [20,50,100,200,400]:
        a = a269021(n)
        normalized = mp.mpf(a)*mp.pi*mp.exp(2)/(mp.mpf(16)**n*math.factorial(n-1))
        approximations = [sum(mp.mpf(x.numerator)/x.denominator/mp.mpf(n)**i
                              for i,x in enumerate(d[:M+1])) for M in [0,1,3,5]]
        errors = [approx/normalized-1 for approx in approximations]
        rows.append([n,mp.nstr(normalized,30),*[mp.nstr(e,15) for e in errors]])
    write_csv(out/'asymptotic_checks.csv', ['n','normalized_exact',
                'relative_error_M0','relative_error_M1','relative_error_M3','relative_error_M5'], rows)
    # Uniform coefficients also checked away from the diagonal at rho=1/2,2.
    general_rows = []
    for rho in [Fraction(1,2),Fraction(1),Fraction(2)]:
        for k in [50,100,200]:
            m = k*rho
            assert m.denominator == 1
            n = k+m.numerator
            base = Fraction(math.factorial(n)**2,math.factorial(k)**2*math.factorial(n-k))
            s = mp.mpf(first_moment(n,k))*base.denominator/base.numerator*mp.exp(2*float(rho))
            c1=2*rho-rho*rho
            c2=rho*(3*rho**3-20*rho**2+42*rho+2)/6
            ap=1+mp.mpf(c1.numerator)/c1.denominator/k+mp.mpf(c2.numerator)/c2.denominator/k**2
            general_rows.append([str(rho),k,n,mp.nstr(s,24),mp.nstr((s-ap)*k**3,15)])
    write_csv(out/'uniform_checks.csv',['rho','k','N','e2rho_C1_over_B','k3_residual_after_c2'],general_rows)
    return {'precision_decimal_digits':100,'diagonal_n':[20,50,100,200,400],
            'uniform_checks':len(general_rows)}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parent/'results')
    parser.add_argument('--core-only',action='store_true',help='Skip optional SymPy and mpmath checks.')
    parser.add_argument('--symbolic-only',action='store_true',help='Regenerate only symbolic and numerical checks.')
    args=parser.parse_args()
    args.output.mkdir(parents=True,exist_ok=True)
    start=perf_counter()
    report={'status':'passed','proof_status':'conventional proof; tests are not formal verification'}
    if not args.symbolic_only:
        report['exact']=exact_tests(args.output)
        print('Exact checks passed', flush=True)
    if not args.core_only:
        report['symbolic']=symbolic_tests(args.output)
        print('Symbolic checks passed', flush=True)
        report['numerical']=numerical_tests(args.output)
    report['elapsed_seconds']=round(perf_counter()-start,3)
    (args.output/'verification_summary.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    main()
