#!/usr/bin/env python3
"""Reproduce exact identities and numerical diagnostics in the article.

No network access is used. Floating-point tests are diagnostics, not interval
certificates. The uniform estimates are established by proofs in article.tex.
Output paths are relative to this script, not the caller's working directory.
"""
from __future__ import annotations

import argparse
import json
from decimal import Decimal, ROUND_CEILING
from pathlib import Path
from typing import Any

import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parent


def exact_checks() -> dict[str, Any]:
    s, v, q = sp.symbols('s v q')
    def trunc(expr: sp.Expr, order: int) -> sp.Expr:
        return sp.series(expr, s, 0, order).removeO().expand()
    tc = (s**2/2+s**3/3-s**4/8-3*s**5/10+s**6/48
          +sp.Rational(323,840)*s**7+sp.Rational(1123,5760)*s**8)
    h = lambda x: -sum(x**j/sp.Integer(j) for j in range(2,10))
    k = lambda x: -x-sum(sp.Rational(j+1,j)*x**j for j in range(2,10))
    assert trunc(k(tc)-h(s),9) == 0
    rho = trunc(sp.exp(tc-s)/(1-s)*tc/(1-tc)/s**2,6)
    expected_rho = (sp.Rational(1,2)+s/3+5*s**2/8+7*s**3/10
                    +19*s**4/24+sp.Rational(361,420)*s**5)
    assert sp.expand(rho-expected_rho) == 0
    profiles = [q,
        sp.Rational(1,2)+q/3-5*q**2/6,
        sp.Rational(1,3)-49*q/72-5*q**2/9+65*q**3/72,
        -sp.Rational(1,8)-799*q/1080+9*q**2/8+65*q**3/72-157*q**4/135,
        -sp.Rational(3,10)+22739*q/51840+31*q**2/18
        -3373*q**3/1728-628*q**4/405+28369*q**5/17280]
    # Polynomial s-expansion of Phi; substitute successively to avoid swell.
    M=4
    phi=trunc(sum((s*(v-1))**j/sp.factorial(j) for j in range(M+1))
              *sum(s**j for j in range(M+1))
              *sum(-(v**j-1)*s**(j-2)/sp.Integer(j) for j in range(2,M+3)),M+1)
    P=[phi.coeff(s,j) for j in range(M+1)]
    V=q
    for j in range(1,M+1):
        residual=trunc(sum(s**i*P[i].subs(v,V) for i in range(j+1))
                       -rho*(1-q*q),j+1).coeff(s,j)
        generated=sp.cancel(residual/q).expand()
        assert sp.expand(generated-profiles[j]) == 0
        assert sp.degree(generated,q) <= j+1
        assert generated.subs(q,1) == 0
        V += s**j*generated
    beta = trunc(sp.sqrt(2*(tc/s**2)*(1-tc)/(1+tc-tc**2)),5)
    assert sp.expand(beta-sum(sp.diff(p,q).subs(q,0)*s**j
                              for j,p in enumerate(profiles))) == 0
    logrho=trunc(sp.log(2*rho),4)
    assert logrho == 2*s/3+37*s**2/36+539*s**3/810
    # Explicit rational majorants, using exp(x) <= 1/(1-x).
    r=sp.Rational(1,100)
    E=1/((1-3*r)*(1-r))
    rem=r/3*(8/(1-2*r)+1/(1-r))
    phi_bound=sp.Rational(5,2)*(E-1)+E*rem
    deriv_bound=2*(E-1)+E*(4*r/(1-2*r)+r*(sp.Rational(5,2)+rem))
    assert phi_bound < sp.Rational(7,50)
    assert deriv_bound < sp.Rational(4,25)
    tc_bound=r/(3*(1-r))+3*r*r/(2*(1-r*r))
    L=r*r*(1+1/(2*(1-r)))
    Ecrit=1/(1-L)
    rho_bound=tc_bound*Ecrit/(1-r*r)+sp.Rational(1,2)*(Ecrit/(1-r*r)-1)
    assert rho_bound < sp.Rational(1,250)
    # Reversion of U(s)=s sqrt(2 rho(s)).
    u=sp.symbols('u')
    J=u-u*u/3-25*u**3/72+137*u**4/540+6529*u**5/17280
    U=trunc(s*sp.sqrt(2*rho),6)
    assert sp.series(U.subs(s,J)-u,u,0,6).removeO().expand() == 0
    return {'all_exact_checks_passed':True,
            'tc_through_degree_8':str(tc), 'rho_through_degree_5':str(rho),
            'profile_polynomials':[str(p) for p in profiles],
            'beta_through_degree_4':str(beta), 'log_2rho':str(logrho),
            'branch_reversion':str(J),
            'rational_majorants':{'Phi_error':str(phi_bound),
                'derivative_error':str(deriv_bound),'rho_error':str(rho_bound)}}


def critical_data(s: mp.mpf | mp.mpc) -> tuple[Any,Any]:
    h=lambda t: t+mp.log1p(-t)
    k=lambda t: h(t)-t/(1-t)
    tc=mp.findroot(lambda t:k(t)-h(s), s*s/2, tol=mp.mpf('1e-85'))
    rho=mp.exp(tc-s)/(1-s)*tc/((1-tc)*s*s)
    return tc,rho


def profile_polynomials(q: Any) -> list[Any]:
    return [q, mp.mpf(1)/2+q/3-5*q*q/6,
      mp.mpf(1)/3-49*q/72-5*q*q/9+65*q**3/72,
      -mp.mpf(1)/8-799*q/1080+9*q*q/8+65*q**3/72-157*q**4/135,
      -mp.mpf(3)/10+22739*q/51840+31*q*q/18
      -3373*q**3/1728-628*q**4/405+28369*q**5/17280]


def normalized_coefficient(n: int, s: Any) -> Any:
    """Compute a_n(s) by scalar Lagrange inversion, O(n^2) operations."""
    if n < 1:
        raise ValueError('n must be positive')
    a=s/(1-s)
    J=[mp.mpf(1)]+[a**(j-1)/((1-s)*(j+1)) for j in range(1,n)]
    C=[mp.mpf(1)]
    for k in range(1,n):
        C.append(mp.fsum(((1-n)*j-k)*J[j]*C[k-j]
                         for j in range(1,k+1))/k)
    ek=mp.mpf(1)
    total=C[n-1]
    for j in range(1,n):
        ek *= (-n*s)/j
        total += ek*C[n-1-j]
    return (-1)**n*(1-s)**(2*n)*total/n


def numerical_checks(quick: bool) -> dict[str,Any]:
    mp.mp.dps=100
    profiles=[]
    for sval,qval in [('0.001','0'),('0.001','0.25'),
                      ('0.004','0.1'),('-0.004','0.25'),
                      ('0.001','0.000001')]:
        s,q=mp.mpf(sval),mp.mpf(qval)
        tc,rho=critical_data(s)
        z=s*s*rho*(1-q*q)
        pol=profile_polynomials(q)
        approx=s*(mp.fsum(s**j*pol[j] for j in range(5))-1)
        if q == 0:
            actual=tc-s
        else:
            h=lambda t:t+mp.log1p(-t)
            func=lambda t:mp.exp(t-s)/(1-s)*(h(t)-h(s))-z
            t0=s+approx
            t=mp.findroot(func,(t0,t0+s*mp.mpf('1e-12')),tol=mp.mpf('1e-85'))
            actual=t-s
        error=abs(actual-approx)
        bound=2*abs(s)*(100*abs(s))**5/(1-100*abs(s))
        assert error <= bound
        profiles.append({'s':sval,'q':qval,'N':4,
            'absolute_error':mp.nstr(error,18),'proved_bound':mp.nstr(bound,18),
            'delta':mp.nstr(actual,30)})
    crossover=[]
    orders=[100,200] if quick else [100,200,400]
    for tauval in ['-0.5','0.5','1.0']:
        tau=mp.mpf(tauval)
        for n in orders:
            if abs(tau/n) > mp.mpf('0.005'):
                continue
            s=tau/n
            an=normalized_coefficient(n,s)
            a0=-mp.power(2,n-1)*mp.gamma(n-mp.mpf('0.5'))/(mp.sqrt(mp.pi)*mp.gamma(n+1))
            ratio=an/a0
            leading=mp.exp(-2*tau/3)
            corrected=leading*(1+(tau/3-37*tau*tau/36)/n)
            crossover.append({'tau':tauval,'n':n,'s':mp.nstr(s,16),
                'ratio':mp.nstr(ratio,22),'limit':mp.nstr(leading,22),
                'first_correction':mp.nstr(corrected,22),
                'corrected_error':mp.nstr(abs(ratio-corrected),12)})
    # Independently check the first three known rational sector coefficients.
    s=mp.mpf('0.003'); w=s-1
    bn=[-w*w/(w+1),
        -w**3*(2*w*w+2*w-1)/(2*(w+1)**3),
        -w**4*(9*w**4+18*w**3-11*w+1)/(6*(w+1)**5)]
    for n,b in enumerate(bn,1):
        assert abs(normalized_coefficient(n,s)-s**(2*n-1)*b) < mp.mpf('1e-90')
    # A resonant discriminant: q1^2 - q2 + q1^3, mu=(1,2).
    X=mp.mpf(8); q1=mp.exp(-X); q2=mp.exp(-2*X)
    D=q1*q1-q2+q1**3
    assert abs(mp.sqrt(D)/mp.exp(-mp.mpf('1.5')*X)-1) < mp.mpf('1e-90')
    return {'precision_decimal_digits':100,'profile_tests':profiles,
            'crossover_tests':crossover,'resonance_check_passed':True,
            'first_three_sector_checks_passed':True,
            'qualification':'Floating-point diagnostics; not interval certificates.'}


def write_tables(data: dict[str,Any]) -> None:
    out=ROOT/'data'; out.mkdir(exist_ok=True)
    def upper_scientific(value: str) -> str:
        x = Decimal(value)
        quantum = Decimal(1).scaleb(x.adjusted() - 3)
        return format(x.quantize(quantum, rounding=ROUND_CEILING), '.3E').lower()
    p=[]
    for row in data['numerical']['profile_tests']:
        p.append(f"{row['s']} & {row['q']} & \\num{{{float(row['absolute_error']):.3e}}} & \\num{{{upper_scientific(row['proved_bound'])}}}" + " " + chr(92)*2)
    (out/'profile_table.tex').write_text('\n'.join(p)+'\n')
    p=[]
    for row in data['numerical']['crossover_tests']:
        p.append(f"{row['tau']} & {row['n']} & {float(row['ratio']):.9f} & {float(row['limit']):.9f} & \\num{{{float(row['corrected_error']):.2e}}}" + " " + chr(92)*2)
    (out/'crossover_table.tex').write_text('\n'.join(p)+'\n')


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick',action='store_true',help='omit the n=400 diagnostics')
    args=parser.parse_args()
    data={'exact':exact_checks(),'numerical':numerical_checks(args.quick),
          'versions':{'sympy':sp.__version__,'mpmath':mp.__version__}}
    out=ROOT/'data'; out.mkdir(exist_ok=True)
    (out/'verification.json').write_text(json.dumps(data,indent=2)+'\n')
    write_tables(data)
    print(json.dumps(data,indent=2))

if __name__=='__main__':
    main()
