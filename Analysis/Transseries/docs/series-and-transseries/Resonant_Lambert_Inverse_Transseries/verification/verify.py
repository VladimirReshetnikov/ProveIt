#!/usr/bin/env python3
"""Finite exact checks and numerical diagnostics for the accompanying article.

These tests do not replace the all-order proofs. Numerical checks are ordinary
floating point, not interval certificates. Run without network access:
    python verification/verify.py --output verification/results.json
"""
from __future__ import annotations
import argparse
import json
import math
import platform
from pathlib import Path
from typing import Any
import mpmath as mp
import sympy as sp


def convolution(a: list[Any], b: list[Any], n: int) -> list[Any]:
    c = [sp.S.Zero] * (n + 1)
    for i, ai in enumerate(a[:n + 1]):
        if ai == 0:
            continue
        for j, bj in enumerate(b[:n + 1 - i]):
            if bj != 0:
                c[i + j] += ai * bj
    return [sp.expand(x) for x in c]


def exact_coefficients(N: int = 8) -> tuple[dict[str, Any], list[Any]]:
    u = sp.Symbol('u')
    r = [sp.S.Zero] + [(-1)**n * sp.zeta(1 - n)**2 / sp.factorial(n)
                       for n in range(1, N + 1)]
    powers = [[sp.S.One] + [sp.S.Zero] * N]
    for k in range(1, N + 1):
        powers.append(convolution(powers[-1], r, N))
    C = [sp.S.Zero]
    for n in range(1, N + 1):
        cn = 0
        for k in range(1, n + 1):
            derivative_factor = sum(sp.binomial(k - 1, j) * n**(k - 1 - j)
                                    * sp.rf(k, j) * (u / 2)**j
                                    for j in range(k))
            cn -= u**k * powers[k][n] * derivative_factor / sp.factorial(k)
        C.append(sp.expand(cn))
    # Independent substitution via the differential recurrence for exp(-m V).
    V2 = convolution(C, C, N)
    residual = [C[n] + u * V2[n] / 2 for n in range(N + 1)]
    for m in range(1, N + 1):
        E = [sp.S.One]
        for n in range(1, N - m + 1):
            E.append(sp.expand(-sp.Rational(m, n)
                       * sum(j * C[j] * E[n - j] for j in range(1, n + 1))))
        for n in range(m, N + 1):
            residual[n] += u * r[m] * E[n - m]
    assert all(sp.expand(x) == 0 for x in residual)
    checks = []
    for n in range(1, N + 1):
        p = sp.Poly(C[n], u)
        valuation = min(mon[0] for mon, coef in p.terms() if coef)
        assert p.degree() == 2 * n - 1
        assert valuation == (2 if n >= 3 and n % 2 else 1)
        assert all((-1)**(n+1) * coef > 0 for coef in p.all_coeffs() if coef)
        top = (-1)**(n+1) * sp.catalan(n-1) / 2**(3*n-1)
        assert p.LC() == top
        if n >= 3 and n % 2:
            assert p.nth(2) == sp.Rational(n, 4) * r[n - 1]
        checks.append({'n': n, 'coefficient': str(C[n]),
                       'degree': p.degree(), 'valuation': valuation,
                       'highest_coefficient': str(top)})
    # Centered Gamma/zeta normalizer through degree 3, with symbolic constants.
    e, g, g1, g2, z2, z3 = sp.symbols('e g g1 g2 z2 z3')
    log_gamma_centered = -2*g*e + z2*e**2/2 - z3*e**3/3
    gamma_series = sp.exp(log_gamma_centered).series(e, 0, 4).removeO()
    a = sp.expand(gamma_series * (sp.Rational(1,2)+g*e-2*g1*e**2+2*g2*e**3))
    a3 = sp.Rational(4,3)*g**3 + 4*g*g1 + 2*g2-z3/6
    assert a.coeff(e, 1) == 0
    assert sp.expand(a.coeff(e, 2)-(z2/4-g*g-2*g1)) == 0
    assert sp.expand(a.coeff(e, 3)-a3) == 0
    return {'status': 'passed', 'inverse_order': N,
            'residual_coefficients_through_q_N': 'all exactly zero',
            'centered_normalizer': 'a0,a1,a2,a3 checked symbolically',
            'coefficients': checks}, C


def core(e: Any, L: Any) -> Any:
    e = mp.mpc(e)
    if e == 0:
        return (L+mp.euler)**2/2 + mp.zeta(2)/2-mp.euler**2-2*mp.stieltjes(1)
    return (mp.gamma(e)*mp.zeta(1+2*e)*mp.exp(e*L)
            + mp.gamma(-e)*mp.zeta(1-2*e)*mp.exp(-e*L)
            + mp.zeta(1-e)*mp.zeta(1+e))


def rcoef(k: int, e: Any = 0) -> Any:
    return (-1)**k*mp.zeta(1+e-k)*mp.zeta(1-e-k)/mp.factorial(k)


def fzero(t: Any, digits: int | None = None) -> Any:
    """Independent, convergent Li_1 sum. Truncation is not an interval bound."""
    if mp.re(t) <= 0:
        raise ValueError('Re(t) must be positive')
    dps = digits or mp.mp.dps
    N = int(mp.ceil((dps+12)*mp.log(10)/mp.re(t)))
    q = mp.exp(-t)
    power = q
    terms = []
    for a in range(1, N+1):
        terms.append(-mp.log1p(-power)/a)
        power *= q
    return mp.fsum(terms)


def fzero_prime(t: Any) -> Any:
    N=int(mp.ceil((mp.mp.dps+12)*mp.log(10)/mp.re(t)))
    q=mp.exp(-t); power=q; terms=[]
    for a in range(1,N+1):
        terms.append(-power/(1-power)); power*=q
    return mp.fsum(terms)


def jump_prime(t: Any) -> Any:
    A=4*mp.pi**2
    N=max(3,int(mp.ceil((mp.mp.dps+8)*mp.log(10)/(A*mp.re(1/t)))))
    ds=divisors(N)
    return 4*mp.pi*1j/t*mp.fsum(ds[n]*mp.exp(-A*n/t) for n in range(1,N+1))


def divisors(N: int) -> list[int]:
    d = [0]*(N+1)
    for a in range(1,N+1):
        for n in range(a,N+1,a):
            d[n] += 1
    return d


def jump(t: Any) -> Any:
    A = 4*mp.pi**2
    N = max(3, int(mp.ceil((mp.mp.dps+8)*mp.log(10)/(A*mp.re(1/t)))))
    d = divisors(N)
    return 4*mp.pi*1j*mp.fsum(d[n]*mp.e1(A*n/t) for n in range(1,N+1))


def numeric_checks() -> dict[str, Any]:
    mp.mp.dps = 70
    A = 4*mp.pi**2
    out: dict[str, Any] = {'precision_digits':70}
    errs=[]
    for e in (mp.mpf('.123'),mp.mpc('.2','.1')):
        for k in range(2,11):
            reflected=(2*(1+(-1)**k*mp.cos(mp.pi*e))/A**k
                       *mp.gamma(k-e)*mp.gamma(k+e)/mp.factorial(k)
                       *mp.zeta(k-e)*mp.zeta(k+e))
            errs.append(abs((rcoef(k,e)-reflected)/reflected))
    assert max(errs)<mp.mpf('1e-60')
    out['functional_equation_max_relative_error']=mp.nstr(max(errs),8)
    parity=[]
    for k in (3,5,7):
        actual=mp.diff(lambda e:rcoef(k,e),0,2)
        expected=2*mp.pi**2*mp.gamma(k)**2/mp.factorial(k)/A**k*mp.zeta(k)**2
        err=abs((actual-expected)/expected)
        assert err<mp.mpf('1e-60')
        parity.append({'k':k,'relative_error':mp.nstr(err,8)})
    out['second_jet']=parity
    e=mp.mpf('1e-8'); L=mp.mpf('3')
    err=abs(core(e,L)-core(0,L))
    assert err<mp.mpf('1e-12')
    out['pole_coalescence_difference_at_epsilon_1e_minus8']=mp.nstr(err,12)
    b=mp.zeta(2)/4-mp.euler**2-2*mp.stieltjes(1)
    c=mp.zeta(2)/2-mp.euler**2-2*mp.stieltjes(1)
    a3=mp.mpf(4)/3*mp.euler**3+4*mp.euler*mp.stieltjes(1)+2*mp.stieltjes(2)-mp.zeta(3)/6
    out['constants']={k:mp.nstr(v,35) for k,v in {'C_star':c,'b':b,'a3':a3}.items()}
    roots=[]
    for X in (10,20,40):
        for lam in (mp.mpf('.5'),mp.mpf('1.5')):
            e=lam/X
            approx=(2*X*mp.asinh(lam/2)/lam-mp.euler
                    -(c+b*lam**2)/(X*mp.sqrt(1+lam**2/4))-2*a3*lam**2/X**2)
            actual=mp.findroot(lambda ell:core(e,ell)-X**2/2,approx)
            roots.append({'X':X,'lambda':str(lam),'core_root':mp.nstr(actual,22),
                          'X_cubed_times_error':mp.nstr((actual-approx)*X**3,14)})
    out['uniform_core_inverse']=roots
    # Coalescing critical points of the core only, not of the full Lambert function.
    folds=[]
    D=3*mp.euler**2+6*mp.stieltjes(1)-mp.zeta(2)/2
    def G(w,lam,u):
        return u*u*core(lam*u,w/u-mp.euler)-mp.mpf('.5')
    for u in (mp.mpf('.04'),mp.mpf('.02')):
        w,lam=mp.findroot(lambda w,la:(G(w,la,u),mp.diff(lambda v:G(v,la,u),w)),
                        (mp.pi/2,2j))
        pred_lam=2j*(1+D*u*u)
        pred_w=mp.pi/2*(1-D*u*u)+8*a3*u**3
        folds.append({'u':str(u),'lambda':mp.nstr(lam,25),
                      'lambda_error_div_u4':mp.nstr((lam-pred_lam)/u**4,14),
                      'w_error_div_u4':mp.nstr((w-pred_w)/u**4,14)})
    out['core_folds']=folds
    # Direct sums versus the eighth-order asymptotic expansion.
    table=[]
    for t in (mp.mpf('.1'),mp.mpf('.2'),mp.mpf('.4')):
        exact=fzero(t)
        approx=core(0,-mp.log(t))+sum(rcoef(k)*t**k for k in range(1,9))
        table.append({'t':str(t),'F0':mp.nstr(exact,25),
                      'error':mp.nstr(exact-approx,14),
                      'error_over_t10':mp.nstr((exact-approx)/t**10,14)})
    out['direct_sum_asymptotics']=table
    return out


def mellin_diagnostic() -> dict[str, Any]:
    """Independent adaptive quadrature, using SciPy only in this optional check."""
    try:
        import scipy
        from scipy.integrate import quad
    except ImportError:
        return {'status':'not run; optional scipy unavailable'}
    mp.mp.dps=30
    A=4*mp.pi**2
    rows=[]
    for t in (1,3):
        def integr(v: float) -> float:
            w=mp.mpc(1.5,v)
            return float(mp.re(-2*mp.pi/w*mp.cot(mp.pi*w/2)
                       *mp.gamma(w)*mp.zeta(w)**2*(t/A)**w)/mp.pi)
        val,err=quad(integr,0,55,epsabs=3e-12,epsrel=3e-12,limit=150)
        target=mp.re(fzero(mp.mpf(t))-core(0,-mp.log(t))+mp.mpf(t)/4)
        discrepancy=abs(val-float(target))
        assert discrepancy<1e-10
        rows.append({'t':t,'mellin_integral':val,'direct_sum_remainder':float(target),
                     'absolute_discrepancy':discrepancy,'quadrature_error_estimate':err})
    return {'status':'passed, floating-point only','scipy_version':scipy.__version__,'rows':rows}


def lateral_inverse_diagnostic() -> list[dict[str, Any]]:
    rows=[]
    for t_string,precision in [('1',80),('0.5',125),('0.25',205)]:
        mp.mp.dps=precision
        t=mp.mpf(t_string); A=4*mp.pi**2
        Y=fzero(t)
        jp=jump(t)
        fp=fzero_prime(t)
        initial=t-jp/(2*fp)
        gp=initial
        for _ in range(4):
            gp -= (fzero(gp)+jump(gp)/2-Y)/(fzero_prime(gp)+jump_prime(gp)/2)
        residual=abs(fzero(gp)+jump(gp)/2-Y)
        assert residual<mp.power(10,-precision+20)
        gm=mp.conj(gp)
        split=gp-gm
        bias=(gp+gm)/2-t
        split0=4*mp.pi*1j/A*t*t/(mp.euler-mp.log(t))*mp.exp(-A/t)
        bias0=-t*t/(mp.euler-mp.log(t))**2*mp.exp(-2*A/t)
        rows.append({'t':str(t),'digits':precision,
                     'relative_split_to_leading':mp.nstr(split/split0,18),
                     'relative_bias_to_leading':mp.nstr(bias/bias0,18),
                     'root_residual':mp.nstr(residual,8)})
    return rows


def main() -> None:
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,default=Path('results.json'))
    p.add_argument('--skip-lateral',action='store_true',help='omit higher-precision root diagnostics')
    args=p.parse_args()
    result={'scope':'finite exact tests and non-interval numerical diagnostics',
            'python':platform.python_version(),'sympy':sp.__version__,'mpmath':mp.__version__}
    result['exact'],_=exact_coefficients()
    print('Exact coefficient and normalizer checks passed.',flush=True)
    result['numerical']=numeric_checks()
    print('Functional equation, jets, core, and fold diagnostics passed.',flush=True)
    result['median_mellin']=mellin_diagnostic()
    print('Median Mellin diagnostic completed.',flush=True)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    if not args.skip_lateral:
        result['lateral_inverses']=lateral_inverse_diagnostic()
        print('Lateral inverse diagnostics passed.',flush=True)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(f'Recorded {args.output}',flush=True)

if __name__=='__main__':
    main()
