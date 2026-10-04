#!/usr/bin/env python3
"""Exact and high-precision checks for Phase-Accurate Complex Reversion.

No network or external datasets are used. Numerical tests are corroboration,
not interval arithmetic certificates. The mathematical proofs are in article.tex.
"""
from __future__ import annotations

import argparse
import json
import math
import platform
from fractions import Fraction as Q
from pathlib import Path
from typing import Callable

import mpmath as mp
import sympy as sp


def binomial(x: Q, n: int) -> Q:
    out = Q(1)
    for j in range(n):
        out *= (x - j) / (j + 1)
    return out


def add(a: list[Q], b: list[Q]) -> list[Q]:
    return [x+y for x,y in zip(a,b)]


def mul(a: list[Q], b: list[Q]) -> list[Q]:
    n = len(a)
    out = [Q(0)] * n
    for i, x in enumerate(a):
        if x:
            for j in range(n-i):
                if b[j]:
                    out[i+j] += x*b[j]
    return out


def power_unit(a: list[Q], p: Q) -> list[Q]:
    if a[0] != 1:
        raise ValueError("power_unit requires constant term 1")
    n = len(a)
    u = a.copy()
    u[0] = Q(0)
    v = [Q(1)] + [Q(0)]*(n-1)
    out = v.copy()
    for j in range(1, n):
        v = mul(v, u)
        c = binomial(p, j)
        out = add(out, [c*x for x in v])
    return out


def times_t(a: list[Q]) -> list[Q]:
    return [Q(0)] + a[:-1]


def coefficient(beta: Q, sigma: Q, n: int) -> Q:
    if n == 0:
        return Q(1)
    return (-1)**n * sigma / n * binomial(beta*n + sigma - 1, n-1)


def exact_checks() -> dict:
    checks = 0
    def check(condition: bool, message: str) -> None:
        nonlocal checks
        if not condition:
            raise AssertionError(message)
        checks += 1

    rows = []
    degree = 16
    for beta in [Q(1,3), Q(1,2), Q(2,3), Q(3,4)]:
        y = [coefficient(beta, Q(1), n) for n in range(degree+1)]
        residual = add(y, times_t(power_unit(y, beta)))
        check(residual == [Q(1)] + [Q(0)]*degree, f"core residual beta={beta}")
        for sigma in [Q(1,2), Q(1), Q(3,2), Q(2), Q(3), Q(5)]:
            calculated = power_unit(y, sigma)
            for n in range(degree+1):
                check(calculated[n] == coefficient(beta, sigma, n),
                      f"power coefficient beta={beta}, sigma={sigma}, n={n}")
            ratio = sigma/(1-beta)
            for n in range(math.floor(ratio)+1):
                c = coefficient(beta,sigma,n)
                check((-1)**n*c > 0, f"nonvanishing phase jet beta={beta}, sigma={sigma}, n={n}")
            if ratio.denominator == 1:
                check(coefficient(beta,sigma,int(ratio)) == (-1)**int(ratio)*(1-beta),
                      "critical constant coefficient")
        Y = [Q(1)] + [Q(0)]*degree
        K = beta*(beta-1)/2
        for k in range(4):
            m = 2**(k+1)-1
            e = [x-z for x,z in zip(Y,y)]
            for n in range(m):
                check(e[n] == 0, f"Newton vanishing beta={beta}, k={k}, n={n}")
            check(e[m] == K**(2**k-1), f"Newton leading constant beta={beta}, k={k}")
            rows.append({"beta":str(beta),"k":k,"m":m,"constant":str(e[m])})
            if k < 3:
                f = add(Y, times_t(power_unit(Y,beta)))
                f[0] -= 1
                fp = [Q(1)] + [Q(0)]*degree
                fp = add(fp,[beta*x for x in times_t(power_unit(Y,beta-1))])
                corr = mul(f,power_unit(fp,Q(-1)))
                Y = [x-z for x,z in zip(Y,corr)]

    # Generic independent perturbative residual, checked against D_F formula.
    f = sp.symbols('f1:6', nonzero=True)
    r = sp.symbols('r0:5')
    t = sp.Symbol('t')
    def deriv(expr: sp.Expr) -> sp.Expr:
        result = 0
        for j in range(len(f)-1):
            result += sp.diff(expr,f[j])*f[j+1]
        for j in range(len(r)-1):
            result += sp.diff(expr,r[j])*r[j+1]
        return sp.cancel(result)
    coeffs = []
    for n in range(1,5):
        expr = r[0]**n/f[0]
        for _ in range(n-1):
            expr = sp.cancel(deriv(expr)/f[0])
        coeffs.append(sp.cancel((-1)**n*expr/sp.factorial(n)))
    u = sum(c*t**(j+1) for j,c in enumerate(coeffs))
    # Only extract the needed coefficient of each finite polynomial power.
    residual = 0
    for j in range(1,5):
        residual += f[j-1]*sp.expand(u**j).coeff(t,4)/sp.factorial(j)
    for j in range(4):
        residual += r[j]*sp.expand(u**j).coeff(t,3)/sp.factorial(j)
    check(sp.cancel(residual) == 0, "generic fourth-order forward residual")
    for order in range(1,4):
        residual = sum(f[j-1]*sp.expand(u**j).coeff(t,order)/sp.factorial(j)
                       for j in range(1,order+1))
        residual += sum(r[j]*sp.expand(u**j).coeff(t,order-1)/sp.factorial(j)
                        for j in range(order))
        check(sp.cancel(residual) == 0, f"generic forward residual order {order}")
    return {"assertions_passed":checks,"newton_leading_terms":rows,
            "generic_inverse_coefficients":[str(c) for c in coeffs],
            "power_core_sigma_2_beta_half":[str(coefficient(Q(1,2),Q(2),n)) for n in range(9)]}


def core(w: mp.mpf | mp.mpc, a: mp.mpf | mp.mpc = mp.mpf(1)):
    # (sqrt(a^2+4w)-a)/2 squared, evaluated on the selected large branch.
    s = (mp.sqrt(a*a+4*w)-a)/2
    return s*s


def newton(w, k: int, beta=mp.mpf('0.5'), a=mp.mpf(1)):
    z = w
    for _ in range(k):
        z -= (z+a*z**beta-w)/(1+a*beta*z**(beta-1))
    return z


def numerical_checks() -> dict:
    mp.mp.dps = 160
    phase_rows = []
    for sigma in [mp.mpf(1), mp.mpf('1.5'), mp.mpf(2)]:
        for w in [16,64,256,1024]:
            g = core(mp.mpf(w))
            row = {"sigma":str(sigma),"w":w,"log_phase_ratio":[],"phase_ratio_minus_one":[]}
            for k in range(3):
                h = newton(mp.mpf(w),k)
                d = -(h**sigma-g**sigma)
                row["log_phase_ratio"].append(mp.nstr(d,24))
                row["phase_ratio_minus_one"].append(mp.nstr(mp.expm1(d),24))
            phase_rows.append(row)
    # The critical sigma=3/2, k=1 normalization tends to exp(3/16).
    w = mp.mpf('1e12')
    ratio = mp.exp(-(newton(w,1)**mp.mpf('1.5')-core(w)**mp.mpf('1.5')))
    limit = mp.exp(mp.mpf(3)/16)
    if abs(ratio-limit) > mp.mpf('2e-6'):
        raise AssertionError("critical normalization limit diagnostic failed")

    # Sector coefficients for z+sqrt(z)+b exp(-z^2), using s=sqrt(z).
    s = sp.Symbol('s')
    funcs: list[Callable] = []
    for n in range(1,6):
        q = 2*s/(2*s+1)
        for _ in range(n-1):
            q = sp.cancel((sp.diff(q,s)-4*n*s**3*q)/(2*s+1))
        funcs.append(sp.lambdify(s,(-1)**n*q/sp.factorial(n),"mpmath"))
    inverse_rows = []
    for w in [mp.mpf(4),mp.mpf(8),mp.mpc(6,1),mp.mpc(10,1)]:
        g = core(w)
        E = mp.exp(-g*g)
        sg = mp.sqrt(g)
        def scaled_eq(v):
            z = g+E*v
            # Rationalized square-root difference prevents loss of significance.
            return v*(1+1/(mp.sqrt(z)+sg)) + mp.exp(-E*v*(2*g+E*v))
        v = mp.findroot(scaled_eq, -1/(1+1/(2*sg)), solver='newton', tol=mp.mpf('1e-145'))
        total = mp.mpc(0)
        errors = []
        next_ratios = []
        for n in range(1,5):
            total += funcs[n-1](sg)*E**(n-1)
            errors.append(mp.nstr(abs(total-v),24))
            next_term = funcs[n](sg)*E**n
            next_ratios.append(mp.nstr(abs((v-total)/next_term),24))
        if abs(scaled_eq(v)) > mp.mpf('1e-130'):
            raise AssertionError("scaled inverse residual diagnostic failed")
        inverse_rows.append({"w":mp.nstr(w,16),"g":mp.nstr(g,24),
                             "scaled_displacement":mp.nstr(v,24),
                             "errors_for_1_to_4_sectors":errors,
                             "error_over_next_sector":next_ratios,
                             "scaled_equation_residual":mp.nstr(abs(scaled_eq(v)),8)})

    # Exact parametrization of a bent equal-magnitude curve.
    phi = mp.pi/4
    b = mp.exp(-mp.j*phi/2)
    curve_rows = []
    for s0 in [25,100,400,1600]:
        z = mp.mpf(s0)*mp.exp(mp.j*phi)
        w = z+mp.sqrt(z)
        rad = abs(w)
        theta = mp.arg(w)
        predicted = phi + b.imag/rad**mp.mpf('0.5') - mp.mpf('0.5')*b.real*b.imag/rad
        curve_rows.append({"source_radius":s0,"target_radius":mp.nstr(rad,20),
                           "angle_shift":mp.nstr(theta-phi,20),
                           "two_term_angle_error":mp.nstr(theta-predicted,20),
                           "exact_boundary_residual":mp.nstr(abs(mp.re(core(w)**2)),8)})

    # Infinite phase jet: log tail evaluated without subtracting e^(1/w).
    height_rows = []
    for w0 in [100,1000,10000]:
        w = mp.mpf(w0)
        n0 = w/mp.lambertw(w*w/mp.e)
        n = int(mp.ceil(n0))
        def log_tail(n):
            # tail begins at degree n, corresponding to truncation at N=n-1.
            term = mp.mpf(1)
            total = term
            for j in range(1,10000):
                term /= w*(n+j)
                total += term
                if abs(term) < mp.mpf('1e-150')*abs(total):
                    break
            return w-mp.loggamma(n+1)-n*mp.log(w)+mp.log(total)
        height_rows.append({"w":w0,"n_lambert":mp.nstr(n0,20),"N_sufficient":n-1,
                            "log_phase_tail":mp.nstr(log_tail(n),20),
                            "log_tail_c_0_4":mp.nstr(log_tail(max(1,int(mp.floor(mp.mpf('0.4')*w/mp.log(w))))),20),
                            "log_tail_c_0_6":mp.nstr(log_tail(max(1,int(mp.ceil(mp.mpf('0.6')*w/mp.log(w))))),20)})

    # Cancellation-free exact error recurrence for beta=1/2, a=1.
    # Here G is evaluated at high precision; these are diagnostics, not intervals.
    moving_rows = []
    for w0 in [16,64,256,1024,4096]:
        w = mp.mpf(w0)
        G = core(w)
        for sigma in [mp.mpf(1),mp.mpf(2)]:
            e = w-G
            found = None
            for k in range(40):
                log_ratio = mp.log(abs(e)) + G**sigma
                if log_ratio <= mp.log(mp.mpf('0.1')):
                    found = {"w":w0,"sigma":str(sigma),"first_k":k,
                             "log_error_over_exp_sector":mp.nstr(log_ratio,20),
                             "m_delta_log_w":mp.nstr((2**(k+1)-1)*mp.log(w)/2,20),
                             "core_phase":mp.nstr(G**sigma,20)}
                    break
                x = G+e
                sx = mp.sqrt(x)
                e = -e*e/((2*sx+1)*(mp.sqrt(G)+sx)**2)
            if found is None:
                raise AssertionError("moving Newton diagnostic did not converge")
            moving_rows.append(found)

    return {"precision_digits":mp.mp.dps,"phase_accuracy":phase_rows,
            "critical_limit":{"w":"1e12","ratio":mp.nstr(ratio,24),"limit":mp.nstr(limit,24)},
            "inverse_sector_tests":inverse_rows,"bent_boundaries":curve_rows,
            "height_two_phase_tails":height_rows,"moving_newton_resolution":moving_rows}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',type=Path,default=Path('build/results'))
    parser.add_argument('--part',choices=['all','exact','numerical'],default='all')
    args = parser.parse_args()
    args.out.mkdir(parents=True,exist_ok=True)
    report = {"python":platform.python_version(),"sympy":sp.__version__,
              "mpmath":mp.__version__,"status":"executed checks, not formal verification"}
    if args.part in ('all','exact'):
        report['exact'] = exact_checks()
    if args.part in ('all','numerical'):
        report['numerical'] = numerical_checks()
    filename = 'verification.json' if args.part=='all' else f'{args.part}.json'
    (args.out/filename).write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(report,indent=2))

if __name__ == '__main__':
    main()
