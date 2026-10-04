#!/usr/bin/env python3
"""Reproduce exact identities and high-precision diagnostics for the article.

No network access or external data are used. Floating-point diagnostics are not
interval certificates. The mathematical bounds are proved in the article.
"""
from __future__ import annotations
import argparse
import json
import math
import platform
from pathlib import Path
import mpmath as mp
import sympy as sp


def poly_mul(a, b, degree):
    c = [sp.S.Zero] * (degree + 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            if i + j <= degree:
                c[i + j] += ai * bj
    return [sp.expand(x) for x in c]


def poly_compose(a, b, degree):
    out = [sp.S.Zero] * (degree + 1)
    power = [sp.S.One] + [sp.S.Zero] * degree
    for ai in a:
        out = [sp.expand(x + ai * y) for x, y in zip(out, power)]
        power = poly_mul(power, b, degree)
    return out


def exact_checks():
    e, x, t, v = sp.symbols('e x t v')
    N = 9
    # Coefficients of Q(x)=-x*exp(x+e*x*x).
    expc = [sp.S.One]
    for n in range(1, N):
        expc.append(sp.expand((expc[n-1] + (2*e*expc[n-2] if n >= 2 else 0))/n))
    forward = [sp.S.Zero] + [-u for u in expc]
    inverse = [sp.S.Zero]
    for n in range(1, N+1):
        cn = sum((-1)**n * (-n*e)**k * (-n)**(n-1-2*k) /
                 (sp.Integer(n)*sp.factorial(k)*sp.factorial(n-1-2*k))
                 for k in range((n-1)//2+1))
        inverse.append(sp.expand(cn))
    residual = poly_compose(forward, inverse, N)
    residual[1] -= 1
    assert all(sp.expand(r) == 0 for r in residual)

    r, A3, A4 = sp.symbols('r A3 A4', nonzero=True)
    b1 = 1/r
    b2 = -A3/(2*r**4)
    b3 = (5*A3**2-4*r**2*A4)/(8*r**7)
    puiseux = b1*v+b2*v**2+b3*v**3
    res = sp.series(r**2*puiseux**2+A3*puiseux**3+A4*puiseux**4-v**2, v, 0, 5).removeO()
    assert sp.simplify(res) == 0

    v0, v1, v2 = sp.symbols('v0 v1 v2')
    sc = -1+t*v1+t**2*v1*(v2-v1)
    shift = sc+1
    vp = v1+v2*shift
    crit = sp.series(1+sc+t*sc*vp,t,0,3).removeO()
    assert sp.expand(crit) == 0
    logqc = sp.series(sp.log(-sc)+sc+t*(v0+v1*shift+v2*shift**2/2),t,0,3).removeO()
    assert sp.simplify(logqc-(-1+t*v0+t**2*v1**2/2)) == 0

    a, A, s = sp.symbols('a A s', nonzero=True)
    psi = (s+A*a*sp.log(1+s*t/A))/(1+a*t)
    psijet = sp.series(psi,t,0,4).removeO()
    logunit = sp.series(sp.log(psijet/s),t,0,4).removeO().expand()
    target = -a*s*t**2/(2*A)+(a*a*s/(2*A)+a*s*s/(3*A*A))*t**3
    assert sp.simplify(logunit-target) == 0
    # Exact rational certificates for the coarse foreign-sheet scale.
    # exp(x) exceeds every positive Taylor partial sum for rational x > 0.
    for x0, target_exp in [(sp.Rational(2303,1000), 10),
                           (sp.Rational(213,25), 5000)]:
        lower = sum(x0**j / sp.factorial(j) for j in range(41))
        assert lower > target_exp
    assert sp.Rational(213,25) + 1081*sp.Rational(2303,1000) < sp.Rational(4997,2)
    return {
        'lagrange_residual_through_degree': N,
        'lagrange_residual_zero': True,
        'puiseux_identity_through_degree_4': True,
        'critical_envelope_through_parameter_degree_2': True,
        'logarithmic_core_logunit_through_g_inverse_degree_3': True,
        'foreign_sheet_scale_rational_certificate': True,
        'first_inverse_coefficients': [str(c) for c in inverse[1:7]],
        'logunit_jet': str(target),
    }


def coefficient_ratio(n: int, epsilon):
    """Exact terminating formula, evaluated at high precision.

    Returns c_n(epsilon)/c_n(0). The optional numerical early stop is used only
    after successive term ratios have become <1 and terms are negligible.
    """
    if n < 1:
        raise ValueError('n must be positive')
    term = mp.mpf(1)
    total = term
    for k in range(1, (n-1)//2+1):
        ratio = (-epsilon/n)*(n+1-2*k)*(n-2*k)/k
        term *= ratio
        total += term
        if k > 12 and abs(ratio) < mp.mpf('0.5') and abs(term) < mp.mpf('1e-90'):
            break
    return total


def critical_data(epsilon):
    if epsilon == 0:
        sc = mp.mpf(-1)
    else:
        sc = -2/(1+mp.sqrt(1-8*epsilon))
    qc = -sc*mp.exp(sc+epsilon*sc*sc)
    Q = lambda s: -s*mp.exp(s+epsilon*s*s)
    A2 = -mp.diff(Q,sc,2)/(2*qc)
    A3 = -mp.diff(Q,sc,3)/(6*qc)
    A4 = -mp.diff(Q,sc,4)/(24*qc)
    b1 = 1/mp.sqrt(A2)
    b3 = (5*A3*A3-4*A2*A4)/(8*mp.power(A2,mp.mpf('3.5')))
    correction = mp.mpf(3)/8-3*b3/(2*b1)
    return sc, qc, b1, correction


def serial(z, digits=35):
    if isinstance(z, mp.mpc):
        return {'real':mp.nstr(z.real,digits),'imag':mp.nstr(z.imag,digits)}
    return mp.nstr(z,digits)


def numerical_checks():
    mp.mp.dps = 110
    cases = []
    for name, epsilon in [('real',mp.mpf('0.0001')),
                          ('complex',mp.mpc('0.00005','0.00005'))]:
        sc,qc,b1,d1 = critical_data(epsilon)
        rows = []
        for n in [25,100,400,1600]:
            # c_n(0) = -n^(n-1)/n!; scaled evaluation avoids loss of range.
            norm = -coefficient_ratio(n,epsilon)*mp.exp((n-1)*mp.log(n)-mp.loggamma(n+1)
                    +n*mp.log(qc)+mp.mpf('1.5')*mp.log(n))
            lead = -b1/(2*mp.sqrt(mp.pi))
            rel = norm/lead-1
            refined = norm/(lead*(1+d1/n))-1
            rows.append({'n':n,'scaled_coefficient':serial(norm),
                         'relative_leading_error':serial(rel),
                         'relative_two_term_error':serial(refined)})
        cases.append({'case':name,'epsilon':serial(epsilon),'critical_point':serial(sc),
                      'critical_value':serial(qc),'b1':serial(b1),
                      'relative_1_over_n_coefficient':serial(d1),
                      'analytic_sup_bound_for_V_on_radius_1_5':serial(abs(epsilon)*mp.mpf('2.25')),
                      'required_sup_bound':serial(mp.mpf('0.00025')),
                      'late_coefficients':rows})
    eps=mp.mpf('0.0001')
    sc,qc,b1,_ = critical_data(eps)
    far=(-1-mp.sqrt(1-8*eps))/(4*eps)
    logfar=mp.log(-far)+far+eps*far*far
    foreign={'far_critical_point':serial(far),'log10_far_critical_value':serial(logfar/mp.log(10)),
             'log10_selected_radius':serial(mp.log(qc)/mp.log(10)),
             'log10_ratio_far_to_selected':serial((logfar-mp.log(qc))/mp.log(10))}
    tails=[]
    partial=mp.mpf(0)
    for n in range(1,2001):
        partial -= coefficient_ratio(n,eps)*mp.exp((n-1)*mp.log(n)-mp.loggamma(n+1)+n*mp.log(qc))
        if n in [125,500,2000]:
            tails.append({'N':n,'sqrt_N_times_boundary_tail':serial(mp.sqrt(n)*(sc-partial)),
                          'limit':serial(-b1/mp.sqrt(mp.pi))})
    a=mp.mpf(2); g=mp.mpf(100); R=mp.mpf('1.5')
    psi=lambda s: (s+a*mp.log1p(s/g))/(1+a/g)
    psip=lambda s: (1+a/(g+s))/(1+a/g)
    scg=mp.findroot(lambda s:psi(s)+psip(s),(-mp.mpf('1.01'),-mp.mpf('0.99')))
    qcg=-mp.exp(scg)*psi(scg)
    K=a/((1+a/g)*(g-R)**2)
    bound=-mp.log(1-R*K/2)
    assert bound < mp.mpf('0.00025')
    logcore={'a':serial(a),'g':serial(g),'critical_point':serial(scg),'critical_value':serial(qcg),
             'proved_logunit_sup_bound':serial(bound),
             'required_bound':serial(mp.mpf('0.00025')),
             'third_order_radius_approximation':serial(mp.exp(-1)*(1+a/(2*g*g)+(-a*a/2+a/3)/g**3)),
             'critical_equation_residual':serial(abs(psi(scg)+psip(scg)))}
    crossover=[]
    for n in [1000,4000,16000]:
        ep=mp.mpf(1)/n
        crossover.append({'n':n,'epsilon':serial(ep),'n_epsilon':1,
                          'coefficient_ratio':serial(coefficient_ratio(n,ep)),
                          'limit':serial(mp.exp(-1)),
                          'sufficient_theorem_bound_holds': bool(ep*mp.mpf('2.25')<=mp.mpf('0.00025'))})
    return {'precision_decimal_digits':mp.mp.dps,'quadratic_phase_cases':cases,
            'foreign_sheet_example':foreign,'boundary_tails':tails,
            'logarithmic_core_example':logcore,'double_scaling':crossover}


def make_figures(folder: Path):
    import numpy as np
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    folder.mkdir(parents=True,exist_ok=True)
    ep=complex(0.00005,0.00005)
    sc=complex(critical_data(mp.mpc(ep))[0]); tau=abs(sc)
    theta=np.linspace(-math.pi,math.pi,1201)
    s=sc*np.exp(1j*theta)
    q=-s*np.exp(s+ep*s*s)
    qc=-sc*np.exp(sc+ep*sc*sc)
    fig,ax=plt.subplots(figsize=(7.4,3.9),layout='constrained')
    ax.plot(theta,np.log(abs(q)/abs(qc)),label=r'$\log(|Q(s_c e^{it})|/|q_c|)$')
    ax.axhline(0,linestyle='--',linewidth=0.8)
    ax.set_xlabel(r'Angular displacement $t$ from the critical point')
    ax.set_ylabel('Logarithmic modulus gap')
    ax.set_title('The critical circle has a unique minimum')
    ax.legend(); ax.grid(alpha=0.2)
    fig.savefig(folder/'critical_circle.png',dpi=180)
    plt.close(fig)
    ns=np.arange(1000,20001,500)
    fig,ax=plt.subplots(figsize=(7.4,3.9),layout='constrained')
    for epstr in ['0.0001','0.00005']:
        eps=mp.mpf(epstr)
        xs=[float(n*eps) for n in ns]
        ys=[float(coefficient_ratio(int(n),eps)) for n in ns]
        ax.plot(xs,ys,marker='.',markersize=3,label=r'$\epsilon='+epstr+'$')
    xx=np.linspace(0,2,300)
    ax.plot(xx,np.exp(-xx),linestyle='--',label=r'Limit $e^{-\lambda}$')
    ax.set_xlabel(r'$\lambda=n\epsilon$')
    ax.set_ylabel(r'$c_n(\epsilon)/c_n(0)$')
    ax.set_title('A small phase correction has an order-one late-sector effect')
    ax.legend(); ax.grid(alpha=0.2)
    fig.savefig(folder/'late_sector_crossover.png',dpi=180)
    plt.close(fig)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',type=Path,default=Path('results/reproduced'))
    parser.add_argument('--figures',type=Path,default=None)
    args=parser.parse_args()
    result={'environment':{'python':platform.python_version(),'sympy':sp.__version__,'mpmath':mp.__version__},
            'status':'All exact assertions passed; numerical results are diagnostics, not interval proofs.',
            'exact':exact_checks(),'numerical':numerical_checks()}
    args.out.mkdir(parents=True,exist_ok=True)
    (args.out/'verification.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    if args.figures is not None:
        make_figures(args.figures)
    print(result['status'])
    print('Results:',args.out/'verification.json')

if __name__=='__main__':
    main()
