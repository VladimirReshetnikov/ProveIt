#!/usr/bin/env python3
"""Reproduce the exact checks in the A321941 arithmetic-conjectures article.

Python >=3.10.  The main recurrence and independent published recurrence use
only the standard library. SymPy and mpmath are optional for the additional
symbolic and numerical checks. Run without -O: assertions are deliberate tests.
These finite checks are not substitutes for the all-orders proofs in article.tex.
"""
from __future__ import annotations
import argparse
import csv
import json
import platform
import sys
import time
from fractions import Fraction
from functools import lru_cache
from math import comb, prod
from pathlib import Path

F = Fraction

@lru_cache(maxsize=None)
def half_choose(j: int, m: int) -> Fraction:
    """The exact binomial coefficient binom(1/2-j,m)."""
    if j < 0 or m < 0:
        raise ValueError("j and m must be nonnegative")
    v = F(1)
    for i in range(m):
        v *= F(1 - 2*j - 2*i, 2*(i+1))
    return v

@lru_cache(maxsize=None)
def operator_weight(j: int, delta: int, kind: str) -> int:
    """Integer coefficient of the even/odd shift operator; delta must be even."""
    if delta < 0 or delta % 2 or kind not in ("E", "O"):
        raise ValueError("Invalid operator index")
    m = delta + (2 if kind == "E" else 1)
    v = (8 if kind == "E" else 2)*half_choose(j, m)*64**delta
    assert v.denominator == 1
    return v.numerator

def convolution(a: list, b: list, n: int):
    return sum(a[j]*b[n-j] for j in range(n+1))

def integer_coefficients(order: int, parameter: int = 1) -> list[int]:
    """Compute P_0(parameter),...,P_order(parameter) by the nonlinear recurrence."""
    if order < 0 or not isinstance(parameter, int):
        raise ValueError("order must be nonnegative and parameter an integer")
    r, e, o, tau = [1], [-1], [1], [1]
    for n in range(1, order+1):
        m = n-1
        H = (-4*parameter*convolution(r, r, m)
             + 2*convolution(r, e, m)-convolution(tau, tau, m))
        cross = sum(r[j]*r[n-j] for j in range(1, n))
        assert cross % 4 == 0
        rn = 2*H-cross//2
        assert rn % 2 == 0
        r.append(rn)
        en = sum(r[j]*operator_weight(j, n-j, "E")*parameter**((n-j)//2)
                 for j in range(n % 2, n+1, 2))
        on = sum(r[j]*operator_weight(j, n-j, "O")*parameter**((n-j)//2)
                 for j in range(n % 2, n+1, 2))
        e.append(en)
        o.append(on)
        tau.append(on-32*parameter*tau[-1])
    return r

@lru_cache(maxsize=None)
def rising_coefficient(j: int, ell: int) -> Fraction:
    """(j+1/2)_ell / ell!, the coefficient of (1-h)^(-j-1/2)."""
    if ell < 0:
        return F(0)
    value = F(1)
    for i in range(ell):
        value *= F(2*j+1+2*i, 2*(i+1))
    return value

def published_coefficients(order: int) -> list[Fraction]:
    """Independent implementation of Brent--Glasser--Guttmann, Lemma 14 (2019)."""
    d = [F(1)]
    polynomials = ((1, (-6,13,-7,1)), (2, (6,-19,17,-3)),
                   (3, (-2,11,-17,6)))
    for k in range(1, order+1):
        total = F(0)
        for j in range(k):
            exponent = k+2-j
            coeff = F(0)
            for a, poly in polynomials:
                coeff += sum(poly[ell]*a**(exponent-ell)
                             *rising_coefficient(j, exponent-ell)
                             for ell in range(min(3, exponent)+1))
            total += d[j]*coeff
        d.append(-total/(8*k))
    return d

def valuation_two(value: int) -> int:
    if value == 0:
        raise ValueError("2-adic valuation of zero is not finite")
    v, value = 0, abs(value)
    while value % 2 == 0:
        value //= 2
        v += 1
    return v

def odd_double_factorial(n: int) -> int:
    if n == -1:
        return 1
    if n < 1 or n % 2 == 0:
        raise ValueError("Expected a positive odd integer or -1")
    return prod(range(1, n+1, 2))

def symbolic_checks(r: list[int], out: Path) -> bool:
    try:
        import sympy as sp
    except ImportError:
        print("SKIP symbolic checks (install sympy)")
        return False
    print("SymPy:", sp.__version__)
    t, z = sp.symbols("t z")
    ps, es, taus = [sp.Integer(1)], [-sp.Integer(1)], [sp.Integer(1)]
    for n in range(1, 9):
        m = n-1
        H = (-4*t*convolution(ps, ps, m)
             +2*convolution(ps, es, m)-convolution(taus, taus, m))
        cross = sum(ps[j]*ps[n-j] for j in range(1, n))
        pn = sp.expand(2*H-cross/2)
        assert all(c.is_Integer and c % 2 == 0 for c in sp.Poly(pn,t).all_coeffs())
        assert sp.degree(pn,t) == n
        assert pn.coeff(t,n) == (-4)**n*comb(2*n,n)
        assert pn.subs(t,0) == -comb(2*n,n)*odd_double_factorial(2*n-3)*odd_double_factorial(2*n+1)
        assert pn.subs(t,1) == r[n]
        difference = sp.Poly(pn-(-1)**n*(4*t+3)**n*comb(2*n,n)
                             -(16 if n == 2 else 0),t)
        assert all(c % 32 == 0 for c in difference.all_coeffs())
        ps.append(pn)
        en = sp.expand(sum(ps[j]*operator_weight(j,n-j,"E")*t**((n-j)//2)
                           for j in range(n%2,n+1,2)))
        on = sp.expand(sum(ps[j]*operator_weight(j,n-j,"O")*t**((n-j)//2)
                           for j in range(n%2,n+1,2)))
        es.append(en)
        taus.append(sp.expand(on-32*t*taus[-1]))
    (out/"polynomials.txt").write_text("\n".join(f"P_{n}(t) = {p}" for n,p in enumerate(ps))+"\n")
    print("PASS polynomial integrality, evenness, degree, both edge formulas, and mod 32: k=0..8")
    Dh = sum(sp.Rational(r[j],64**j)*z**j for j in range(7))
    inverse = [sp.Rational(2,3)*Dh.coeff(z,1)]
    for k in range(1,5):
        coefficient = sp.series(Dh**(-sp.Rational(2*k,3)),z,0,k+2).removeO().expand().coeff(z,k+1)
        inverse.append(-coefficient/k)
    expected = [sp.Rational(-7,48),sp.Rational(-29,2304),sp.Rational(-3719,331776),
                sp.Rational(-1565,32768),sp.Rational(-36355159,191102976)]
    assert inverse == expected
    # Direct composition independently checks the displayed inverse coefficients.
    forward = sp.series(Dh**(-sp.Rational(2,3)),z,0,7).removeO()
    residual = forward/z + inverse[0] - 1/z
    for k in range(1,5):
        residual += inverse[k]*z**k*sp.series(forward**(-k),z,0,5).removeO()
    assert sp.series(residual,z,0,5).removeO().expand() == 0
    print("PASS five displayed inverse coefficients and direct formal composition")
    x0,x1,y0,y1,q=sp.symbols("x0 x1 y0 y1 q")
    pm=x0*y0; p=x1*y1; pp=(q*x1-x0)*(q*y1-y0)
    w=x0*y1-x1*y0
    assert sp.expand(q**4*p**2-2*q**2*p*(pp+pm)+(pp-pm)**2-q**2*w**2)==0
    print("PASS symbolic bilinear invariant")
    return True

def numerical_checks(r: list[int], out: Path) -> bool:
    try:
        import mpmath as mp
    except ImportError:
        print("SKIP numerical checks (install mpmath)")
        return False
    print("mpmath:",mp.__version__)
    bs=[F(-7,48),F(-29,2304),F(-3719,331776),F(-1565,32768),F(-36355159,191102976)]
    def run(digits: int):
        records=[]
        with mp.workdps(digits):
            for n in (25,100,400):
                rho=-mp.exp(-1)*mp.gamma(n)*mp.hyp1f1(n+1,2,1)*mp.hyperu(n,0,1)
                value=-2*mp.mpf(n)**mp.mpf("1.5")*rho
                approximation=sum(mp.mpf(r[k])/64**k/n**k for k in range(6))
                y=(-2*rho)**(-mp.mpf(2)/3)
                inverse_approx=y+sum((mp.mpf(b.numerator)/b.denominator)*y**(-k)
                                     for k,b in enumerate(bs))
                records.append((n,mp.nstr(value,35),mp.nstr(value-approximation,20),
                                mp.nstr(inverse_approx-n,20)))
        return records
    rows=run(80)
    assert rows==run(120)
    with (out/"numerical_checks.csv").open("w",newline="") as f:
        writer=csv.writer(f)
        writer.writerow(("n","normalized_product","error_after_d5","inverse_error_after_b4"))
        writer.writerows(rows)
    for row in rows:
        print("NUM",*row)
    print("PASS displayed numerical values stable between 80 and 120 decimal digits (not interval certificates)")
    return True

def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--order",type=int,default=256)
    parser.add_argument("--independent-order",type=int,default=128)
    parser.add_argument("--out",type=Path,default=Path(__file__).resolve().parent)
    parser.add_argument("--no-optional",action="store_true")
    args=parser.parse_args()
    if args.order<12 or not 0<=args.independent_order<=args.order:
        parser.error("order >=12 and 0 <= independent-order <= order are required")
    if not __debug__:
        parser.error("Run without Python's -O option; assertions must be enabled")
    if hasattr(sys,"set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    args.out.mkdir(parents=True,exist_ok=True)
    print("A321941 verification; Python",platform.python_version())
    start=time.perf_counter()
    r=integer_coefficients(args.order)
    known=[1,-14,86,-3660,-1042202,-247948260,-108448540420,-67825082899288,
           -56771982322924154,-61577812542004343156,-84012331763021201187180,
           -140805160243370476949256616,-284390871665315095422337087524]
    assert r[:13]==known
    print("PASS all 13 displayed OEIS terms")
    for k,rk in enumerate(r):
        assert (rk-comb(2*k,k)-(16 if k in (1,2) else 0))%32==0
        if k and k.bit_count()<=4:
            assert valuation_two(rk)==k.bit_count()
    print(f"PASS integrality/evenness, mod 32, and applicable exact valuations: k=0..{args.order}")
    d=published_coefficients(args.independent_order)
    assert all(d[k]==F(r[k],64**k) for k in range(len(d)))
    print(f"PASS independent published rational recurrence: k=0..{args.independent_order}")
    for t in (-3,-1,0,2,5):
        values=integer_coefficients(48,t)
        for k,v in enumerate(values):
            assert (v-(-1)**k*(4*t+3)**k*comb(2*k,k)-(16 if k==2 else 0))%32==0
    print("PASS parameter congruence: t=-3,-1,0,2,5; k=0..48")
    with (args.out/"coefficients.csv").open("w",newline="") as f:
        writer=csv.writer(f)
        writer.writerow(("k","r_k","d_k_numerator","d_k_denominator","v2_r_k","s2_k"))
        for k,rk in enumerate(r):
            dk=F(rk,64**k)
            writer.writerow((k,rk,dk.numerator,dk.denominator,valuation_two(rk),k.bit_count()))
    print(f"OBSERVATION only: r_k<0 for k=3..{args.order}: {all(x<0 for x in r[3:])}")
    optional={}
    if not args.no_optional:
        optional["symbolic"]=symbolic_checks(r,args.out)
        optional["numerical"]=numerical_checks(r,args.out)
    metadata={"python":platform.python_version(),"exact_order":args.order,
              "independent_order":args.independent_order,"optional_checks":optional,
              "status":"all executed assertions passed","elapsed_seconds":round(time.perf_counter()-start,3)}
    (args.out/"verification_metadata.json").write_text(json.dumps(metadata,indent=2)+"\n")
    print("ALL EXECUTED CHECKS PASSED; elapsed seconds",metadata["elapsed_seconds"])

if __name__=="__main__":
    main()
