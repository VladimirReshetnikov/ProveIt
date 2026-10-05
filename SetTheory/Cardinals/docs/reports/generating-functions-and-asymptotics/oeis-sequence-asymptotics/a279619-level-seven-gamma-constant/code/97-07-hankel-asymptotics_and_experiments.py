#!/usr/bin/env python3
"""Reproduce asymptotic coefficients and exact finite determinant experiments.

Requires SymPy and mpmath. Numerical asymptotic comparisons are illustrations,
not the positivity proof; that proof has its own standard-library checker.
"""
from __future__ import annotations
import csv
import json
from fractions import Fraction
from pathlib import Path
import sympy as sp
from sympy.functions.combinatorial.numbers import stirling
import mpmath as mp
from generate_certificates import formal_ratios
from verify_certificates import sequence, determinant

ROOT = Path(__file__).resolve().parents[1]

def sequence_asymptotics(order: int) -> list[sp.Rational]:
    t = sp.Symbol("t")
    b = [sp.Rational(x.numerator,x.denominator) for x in formal_ratios(order+1)]
    B = sum(b[j]*t**j for j in range(len(b)))
    a = [sp.Integer(1)]
    for m in range(1,order+1):
        A = sum(a[j]*t**j for j in range(len(a)))
        residual = sp.series(B*A-27*(1+t)**(-sp.Rational(3,2))*A.subs(t,t/(1+t)),
                             t,0,m+2).removeO().expand().coeff(t,m+1)
        a.append(sp.cancel(-residual/(27*m)))
    return a

def hankel_coefficients(r: int, alpha: sp.Rational, a: list) -> list:
    order = len(a)-1
    def entry(i: int,j: int,h: int):
        s = i+j
        return sum(a[m]*(-1)**(h-m)*sp.factorial(s)*sp.rf(alpha+m,s+h-m)
                   *stirling(s+h-m,s,kind=2)/sp.factorial(s+h-m)
                   for m in range(h+1))
    matrices = [sp.Matrix(r,r,lambda i,j:entry(i,j,h)) for h in range(order+1)]
    Ginv = matrices[0].inv()
    M = [sp.zeros(r)] + [Ginv*matrices[j] for j in range(1,order+1)]
    power = M[:]
    log = [sp.Integer(0)]*(order+1)
    for p in range(1,order+1):
        for j in range(p,order+1):
            log[j] += sp.Rational((-1)**(p+1),p)*sp.trace(power[j])
        power = [sp.zeros(r)] + [sum((power[k]*M[j-k] for k in range(1,j)),sp.zeros(r))
                                 for j in range(1,order+1)]
    out = [sp.Integer(1)]
    for k in range(1,order+1):
        out.append(sp.cancel(sum(j*log[j]*out[k-j] for j in range(1,k+1))/k))
    return out

def main() -> None:
    a = sequence_asymptotics(4)
    assert a[:3] == [1,-sp.Rational(215,1008),-sp.Rational(1265,290304)]
    expansions = {}
    for r in range(1,7):
        beta = hankel_coefficients(r,sp.Rational(3,2),a)
        expected = -sp.Rational(r*(2*r+1),2)*(r-1+sp.Rational(215,1512))
        assert beta[1] == expected
        expansions[str(r)] = [str(v) for v in beta]
    (ROOT/"data"/"asymptotic_coefficients.json").write_text(
        json.dumps({"a_coefficients":[str(v) for v in a],"hankel_corrections":expansions},indent=2)+"\n")
    c = sequence(1040)
    with (ROOT/"data"/"small_determinants.csv").open("w",newline="") as file:
        writer = csv.writer(file);writer.writerow(["order","shift","determinant"])
        for r in range(1,7):
            for n in range(5):
                value = determinant([[Fraction(c[n+i+j]) for j in range(r)] for i in range(r)])
                assert value.denominator==1
                writer.writerow([r,n,value.numerator])
    # Dodgson condensation: an independent exact integer calculation of signs.
    prev = [1]*262
    cur = c[:261]
    negative_shifts = {}
    for r in range(2,16):
        new = []
        for n in range(len(cur)-2):
            numerator = cur[n]*cur[n+2]-cur[n+1]**2
            denominator = prev[n+2]
            assert denominator != 0
            value,remainder = divmod(numerator,denominator)
            assert remainder == 0
            new.append(value)
        negative_shifts[str(r)] = [n for n in range(min(201,len(new))) if new[n]<0]
        prev,cur = cur,new
    (ROOT/"data"/"finite_sign_experiment.json").write_text(json.dumps(
        {"shift_range":[0,200],"negative_shifts":negative_shifts,
         "warning":"Finite exact data only; no assertion beyond tested shifts/orders."},indent=2)+"\n")
    mp.mp.dps = 100
    C = mp.sqrt(3*mp.pi)/(mp.gamma(mp.mpf(1)/7)*mp.gamma(mp.mpf(2)/7)*mp.gamma(mp.mpf(4)/7))
    with (ROOT/"data"/"asymptotic_errors.csv").open("w",newline="") as file:
        writer = csv.writer(file)
        writer.writerow(["order","shift","relative_error_0","relative_error_1","relative_error_2"])
        for r in (2,3,5):
            H = mp.fprod(mp.factorial(j)*mp.rf(mp.mpf(3)/2,j) for j in range(r))
            for n in (100,500,1000):
                exact = determinant([[Fraction(c[n+i+j]) for j in range(r)] for i in range(r)])
                lead = C**r*mp.mpf(27)**(r*n+r*(r-1))*mp.mpf(n)**(-mp.mpf(r*(2*r+1))/2)*H
                observed = mp.mpf(exact.numerator)/exact.denominator
                errors = []
                for m in range(3):
                    correction = mp.mpf(0)
                    for j in range(m+1):
                        f = Fraction(expansions[str(r)][j]); correction += mp.mpf(f.numerator)/f.denominator/n**j
                    errors.append(mp.nstr((lead*correction-observed)/observed,14))
                writer.writerow([r,n]+errors)
    print("Sequence corrections:",a)
    for r,v in expansions.items(): print("Hankel",r,v[:3])
    print("Finite negative-shift experiment:",negative_shifts)
    print("Wrote exact tables and 100-digit asymptotic comparisons.")

if __name__ == "__main__":
    main()
