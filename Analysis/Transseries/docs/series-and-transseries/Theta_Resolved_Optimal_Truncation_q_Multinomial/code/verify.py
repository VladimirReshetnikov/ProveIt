#!/usr/bin/env python3
"""Reproducible symbolic and numerical diagnostics for the accompanying article.

The analytic theorems are proved in the article. These checks do not replace
proofs and are not interval-arithmetic or Lean certificates. Exact finite-tail
bounds are evaluated with arbitrary-precision floating point and reported.
"""
from __future__ import annotations
import csv
import json
from pathlib import Path
import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
mp.mp.dps = 75
B = 2 * mp.pi

def ms(v):
    return mp.mpf(str(v))

def out(v, n=28):
    return mp.nstr(v, n)

def theta_moments(lam, theta, eta, max_order=6):
    """Unnormalized tilted Gaussian moments; terms outside ~20 sigma omitted."""
    lam, theta, eta = map(ms, (lam, theta, eta))
    if lam <= 0:
        raise ValueError('Use positive lambda for this numerical routine.')
    center = theta + eta / lam
    radius = 20 / lam + 4
    lo, hi = int(mp.floor(center-radius)), int(mp.ceil(center+radius))
    moments = [mp.mpf(0) for _ in range(max_order+1)]
    for k in range(lo, hi+1):
        u = lam * (k-theta)
        w = mp.exp(-u*u/2 + eta*u)
        for j in range(max_order+1):
            moments[j] += w * u**j
    return [v * lam / mp.sqrt(2*mp.pi) for v in moments]

def theta_optimum(lam, theta):
    lam, theta = ms(lam), ms(theta)
    f = lambda eta: theta_moments(lam, theta, eta, 1)[1]
    # Strict convexity gives a unique root. Monotone bisection is robust even
    # for almost integral saddle positions and very small Gaussian weights.
    left, right = -max(lam, 2), max(lam, 2)
    while f(left) >= 0: left *= 2
    while f(right) <= 0: right *= 2
    for _ in range(190):
        mid = (left+right)/2
        if f(mid) < 0: left = mid
        else: right = mid
    eta = (left+right)/2
    m = theta_moments(lam, theta, eta)
    shift = mp.mpf('1.5') - m[4]/(3*m[2]) + eta*m[3]/(2*m[2])
    first = m[3]/3 - eta*m[2]/2
    return eta, m[0], shift, first

def zeta_tail_power(s, start):
    """Upper bound for sum_{n>=start} n^{-s}, s>1."""
    return start**(-s) + start**(1-s)/(s-1)

def remainder_scaled(p, h, x, rays=(1,1), resolved=0, last_pole=14):
    """Return E_L(p;h,x)/[C_beta(z) exp(-beta z)] and a truncation bound.

    Evaluates the positive double sum in log-scaled form. Only h>0 is needed
    for the tabulated experiments. The analytic expression applies to real p.
    """
    p, h, x = map(ms, (p, h, x))
    aa = [ms(a) for a in rays]
    if p < 0 or h <= 0 or x <= 0 or any(a <= 0 for a in aa):
        raise ValueError('Require p>=0, h>0, x>0, positive ray parameters.')
    if not 0 <= resolved < last_pole:
        raise ValueError('Require 0<=resolved<last_pole.')
    amin, total = min(aa), sum(aa)
    mu = sum(a == amin for a in aa)
    z, beta = amin*x, B*(resolved+1)
    pref = mu*mp.sqrt(2*mp.pi)/(beta**mp.mpf('1.5')*mp.sqrt(z))
    tmax = (p+1+24*mp.sqrt(p+1)+260)/z
    M = max(1, int(mp.ceil(tmax/h)))
    val = mp.mpf(0)
    # The ray factor is positive and remains well conditioned at the saddle.
    for m in range(1,M+1):
        t = h*m
        ray_factor = sum(mp.exp(-(a-amin)*x*t) for a in aa) - mp.exp(-(total-amin)*x*t)
        for ell in range(resolved+1,last_pole+1):
            pole = B*ell
            exponent = p*mp.log(t/pole)-z*t+beta*z
            val += 2*h*ray_factor*mp.exp(exponent)/(pole*pole+t*t)/pref
    # Analytic bounds from the finite-evaluation theorem, evaluated numerically.
    C_all = B**(-p-2)*mp.zeta(p+2, resolved+1)
    m_tail = 2*len(aa)*C_all*z**(-p-1)*mp.gammainc(p+1,z*h*M,mp.inf)
    peak = (p/(mp.e*z))**p if p else mp.mpf(1)
    moment = mp.gamma(p+1)/z**(p+1) + h*peak
    ell_tail = 2*len(aa)*B**(-p-2)*zeta_tail_power(p+2,mp.mpf(last_pole+1))*moment
    bound = (m_tail+ell_tail)*mp.exp(beta*z)/pref
    return val, bound

def best_integer(p_prediction, h, x, rays=(1,1), resolved=0):
    middle = max(0,int(mp.nint(p_prediction/2)))
    values = {}
    for K in range(max(0,middle-2),middle+3):
        values[K] = remainder_scaled(2*K,h,x,rays,resolved)
    K = min(values, key=lambda k: values[k][0])
    if K <= 0 or K-1 not in values or K+1 not in values:
        raise ArithmeticError('Predicted candidate window did not bracket optimum.')
    # Intervals here account for sum tails, but not floating point roundoff.
    assert values[K][0]+values[K][1] < values[K-1][0]
    assert values[K][0]+values[K][1] < values[K+1][0]
    return K, values[K][0], values[K][1]

def symbolic_checks():
    e,u,eta = sp.symbols('e u eta')
    exponent = sum((-1)**(j+3)*u**(j+2)*e**j/sp.Integer(j+2)
                   +eta*(-1)**(j+2)*u**(j+1)*e**j/sp.Integer(j+1)
                   for j in range(1,4))
    actual = sp.series(2/(1+(1+e*u)**2)*sp.exp(exponent),e,0,3).removeO().expand()
    P1 = u**3/3-eta*u**2/2-u
    P2 = u**2/2+5*eta*u**3/6+(eta**2/8-sp.Rational(7,12))*u**4-eta*u**5/6+u**6/18
    assert sp.expand(actual.coeff(e,1)-P1) == 0
    assert sp.expand(actual.coeff(e,2)-P2) == 0
    s,t,b = sp.symbols('s t b',positive=True)
    for K in range(9):
        finite = sum((-1)**j*t**(2*j)/b**(2*j+2) for j in range(K))
        tail = (-1)**K*t**(2*K)/(b**(2*K)*(b*b+t*t))
        assert sp.factor(1/(b*b+t*t)-finite-tail) == 0
    th,h = sp.symbols('th h')
    tm,tp = b-h*th,b+h*(1-th)
    log_ratio = sp.series(sp.log(tp/tm),h,0,5).removeO()
    rho = sp.series(h/log_ratio,h,0,3).removeO()
    action = sp.series(tm-rho*sp.log(tm/b),h,0,3).removeO().expand()
    assert sp.simplify(action-b-h*h*th*(1-th)/(2*b)) == 0
    # Gaussian moments of the bounded-offset second correction.
    sigma = sp.symbols('sigma')
    expected = (sigma*sigma-3*sigma+1)/2 + 3*(4*sigma-7)/12 + 15/sp.Integer(18)
    assert sp.simplify(expected-(sigma*sigma/2-sigma/2-sp.Rational(5,12))) == 0
    assert expected.subs(sigma,sp.Rational(1,2)) == -sp.Rational(13,24)
    return {'kernel_finite_identities':9,'P1_P2_exact':True,
            'action_second_order_exact':True,'endpoint_optimum_coefficient':'-13/24'}

def forward_identity_checks():
    x,h = mp.mpf('2.7'),mp.mpf('0.6')
    aa = [mp.mpf(1),mp.mpf(1)]
    w = lambda m: 2*mp.exp(-m*h*x)-mp.exp(-2*m*h*x)
    tail = -mp.fsum(w(m)/(m*mp.expm1(h*m)) for m in range(1,200))
    base = -mp.fsum(w(m)/(h*m*m)-w(m)/(2*m) for m in range(1,200))
    results=[]
    for K in range(0,7):
        correction = -sum(mp.bernoulli(2*k)/mp.factorial(2*k)*h**(2*k-1)
            *mp.fsum(m**(2*k-2)*w(m) for m in range(1,200)) for k in range(1,K+1))
        exact_residual=tail-base-correction
        assert (-1)**(K+1)*exact_residual > 0
        # Independent exact kernel remainder, no pole truncation.
        kernel_sum=mp.mpf(0)
        for m in range(1,200):
            v=h*m
            kr=1/mp.expm1(v)-1/v+mp.mpf('.5')-sum(
                mp.bernoulli(2*k)/mp.factorial(2*k)*v**(2*k-1) for k in range(1,K+1))
            kernel_sum -= w(m)*kr/m
        err=abs(exact_residual-kernel_sum)
        assert err < mp.mpf('1e-68')
        results.append({'K':K,'residual':out(exact_residual),'identity_error':out(err)})
    return results

def write_csv(name, rows):
    # ed. (ProveIt, 2026-09-29): lineterminator='\n' (csv defaults to CRLF) and
    # newline='\n' on the text writers below keep reruns LF on every platform.
    with (ROOT/'data'/name).open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(rows[0]),lineterminator='\n')
        writer.writeheader(); writer.writerows(rows)

def main():
    (ROOT/'data').mkdir(exist_ok=True)
    report={'precision_decimal_digits':mp.mp.dps,'symbolic':symbolic_checks(),
            'forward_identity':forward_identity_checks(),
            'status':'Diagnostics, not a formal proof or interval arithmetic.'}
    rows=[]
    for lam,th in [('1','0.25'),('2','0.25'),('4','0.25'),('4','0.5'),('6','0.25')]:
        lam,th=ms(lam),ms(th)
        eta,M,s,first=theta_optimum(lam,th)
        for n in [8,16,32]:
            h=B/(n+th); z=lam*lam*(n+th)**2/B
            p0=B*z+eta*mp.sqrt(B*z)+s
            K,val,bound=best_integer(p0,h,z)
            near=int(mp.nint(B*z/2))
            unshifted,_=remainder_scaled(2*near,h,z)
            eps=1/mp.sqrt(B*z)
            rows.append(dict(lam=out(lam,6),theta=out(th,6),n=n,z=out(z,10),
                eta_star=out(eta,12),s_star=out(s,12),K_opt=K,K_unshifted=near,
                scaled_minimum=out(val,16),theta_minimum=out(M,16),
                relative_leading_error=out(val/M-1,12),
                relative_corrected_error=out(val/(M+eps*first)-1,12),
                gain_over_unshifted=out(unshifted/val,12),sum_tail_bound=out(bound,6)))
    write_csv('theta_optimization.csv',rows)
    report['theta_cases']=len(rows)
    fixed=[]
    for hh in [B/mp.mpf('2.25'),mp.mpf(4)]:
        beta=B
        m=int(mp.floor(beta/hh)); tm=hh*m; tp=hh*(m+1)
        dm,dp=mp.log(tm/beta),mp.log(tp/beta)
        rho=(tp-tm)/(dp-dm); I=tm-rho*dm
        cm=4*hh/(beta*beta+tm*tm); cp=4*hh/(beta*beta+tp*tp)
        sh=mp.log(-cm*dm/(cp*dp))/(dp-dm)
        for z in [10,25,60]:
            K,val,bound=best_integer(rho*z+sh,hh,z)
            pref=2*mp.sqrt(2*mp.pi)/(beta**mp.mpf('1.5')*mp.sqrt(z))
            actual=val*pref*mp.exp((I-beta)*z)
            C=lambda s: cm*mp.exp(s*dm)+cp*mp.exp(s*dp)
            mid=int(mp.nint((rho*z+sh)/2))
            pred=min(C(2*j-rho*z) for j in range(mid-2,mid+3))
            fixed.append(dict(h=out(hh,12),z=z,action=out(I,16),rho=out(rho,16),
                 K_opt=K,scaled_minimum=out(actual,16),two_atom_prediction=out(pred,16),
                 relative_error=out(actual/pred-1,12),sum_tail_bound=out(bound,6)))
    write_csv('fixed_mesh.csv',fixed)
    report['fixed_mesh_cases']=len(fixed)
    peel=[]
    for L in [0,1,2]:
        beta=B*(L+1); lam=mp.mpf(3); th=mp.mpf('.3'); n=18
        h=beta/(n+th); z=lam*lam*(n+th)**2/beta
        eta,M,s,first=theta_optimum(lam,th)
        K,val,bound=best_integer(beta*z+eta*mp.sqrt(beta*z)+s,h,z,resolved=L)
        peel.append(dict(resolved_poles=L,beta=out(beta,12),z=out(z,12),K=K,
                         ratio_to_theta=out(val/M,14),tail_bound=out(bound,6)))
    write_csv('pole_resolution.csv',peel)
    report['resolved_pole_cases']=len(peel)
    report['all_assertions_passed']=True
    (ROOT/'data'/'verification_results.json').write_text(json.dumps(report,indent=2)+'\n',newline='\n')
    # Small tables are generated directly from the actual computations.
    chosen=[r for r in rows if r['lam'] in ['4.0','6.0'] and r['theta']=='0.25']
    lines=[r'\begin{tabular}{rrrrrr}',r'\toprule',
           r'$\lambda$ & $n$ & $K_0$ & $K_{\min}$ & leading rel. error & gain\\',r'\midrule']
    for r in chosen:
        lines.append(f"{r['lam']} & {r['n']} & {r['K_unshifted']} & {r['K_opt']} & "
                     f"{float(r['relative_leading_error']):.3g} & {float(r['gain_over_unshifted']):.5f} \\\\")
    lines.extend([r'\bottomrule',r'\end{tabular}'])
    (ROOT/'data'/'theta_table.tex').write_text('\n'.join(lines)+'\n',newline='\n')
    lines=[r'\begin{tabular}{rrrrr}',r'\toprule',r'$h$ & $z$ & $I_h$ & $K_{\min}$ & two-atom rel. error\\',r'\midrule']
    for r in fixed:
        lines.append(f"{float(r['h']):.5f} & {r['z']} & {float(r['action']):.7f} & {r['K_opt']} & {float(r['relative_error']):.3g} \\\\")
    lines.extend([r'\bottomrule',r'\end{tabular}'])
    (ROOT/'data'/'fixed_table.tex').write_text('\n'.join(lines)+'\n',newline='\n')
    print(json.dumps({'all_assertions_passed':True,'theta_cases':len(rows),
                      'fixed_mesh_cases':len(fixed),'resolved_pole_cases':len(peel)},indent=2))

if __name__=='__main__': main()
