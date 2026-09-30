#!/usr/bin/env python3
"""Reproduce finite symbolic and high-precision tests for the accompanying paper.

These are consistency checks, not interval certificates or formal proofs.
Run from any working directory; output goes to ../data.
"""
from __future__ import annotations
import argparse
import csv
import json
import platform
from pathlib import Path
import mpmath as mp
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / 'data'

def exact_coefficients(nmax: int) -> tuple[list, list]:
    c = [sp.S.Zero] + [-sp.bernoulli(2*j, sp.Rational(1, 2))/(2*j)
                           for j in range(1, nmax+1)]
    h = [sp.S.Zero]
    for n in range(1, nmax+1):
        q = 2*n-1
        e = [sp.S.One]
        for k in range(1, n+1):
            e.append(sp.expand(sp.Rational(q,k)*sum(j*c[j]*e[k-j]
                                                    for j in range(1,k+1))))
        h.append(-e[n]/q)
    return c,h

def mp_coefficients(nmax: int) -> tuple[list, list]:
    c = [mp.mpf(0)] + [-(mp.power(2, 1-2*j)-1)*mp.bernoulli(2*j)/(2*j)
                            for j in range(1,nmax+1)]
    h = [mp.mpf(0)]
    for n in range(1,nmax+1):
        q = 2*n-1
        e = [mp.mpf(1)]
        for k in range(1,n+1):
            e.append(mp.mpf(q)/k * mp.fsum(j*c[j]*e[k-j] for j in range(1,k+1)))
        h.append(-e[n]/q)
    return c,h

def inverse(x):
    """Exterior inverse branch selected by Newton iteration from x."""
    x = mp.mpc(x) if isinstance(x, (complex, mp.mpc)) else mp.mpf(x)
    w = x - 1/(24*x)
    target = mp.log(x)
    for _ in range(30):
        delta = (mp.digamma(w+mp.mpf('0.5'))-target)/mp.polygamma(1,w+mp.mpf('0.5'))
        w -= delta
        if abs(delta) < 50*mp.eps*max(1,abs(w)):
            return w
    raise ArithmeticError('Newton iteration failed to converge')

def forward_inverse(x, m: int, c: list):
    w = x-1/(24*x)
    for _ in range(30):
        r = mp.log(w/x)+mp.fsum(c[j]*w**(-2*j) for j in range(1,m+1))
        dr = 1/w-mp.fsum(2*j*c[j]*w**(-2*j-1) for j in range(1,m+1))
        delta = r/dr
        w -= delta
        if abs(delta) < 50*mp.eps*max(1,abs(w)):
            return w
    raise ArithmeticError('Forward-truncation Newton iteration failed')

def symbolic_checks() -> dict:
    z, a, b, d = sp.symbols('z a b d')
    c,h = exact_coefficients(14)
    assert h[1:6] == [-sp.Rational(1,24), sp.Rational(3,640),
        -sp.Rational(1525,580608), sp.Rational(615881,199065600),
        -sp.Rational(3058641,504627200)]
    # All finite Laurent residual identities through the checked order.
    p = 1+sum(h[n]*z**n for n in range(1,9))
    residual = sp.series(sp.log(p),z,0,9).removeO()
    for j in range(1,9):
        residual += c[j]*z**j*sp.series(p**(-2*j),z,0,9-j).removeO()
    assert sp.expand(residual).series(z,0,9).removeO() == 0
    # z=1/t, V(t)-t = sum (-1)^n h_n z^(2n-1).
    shift = sum((-1)**n*h[n]*z**(2*n-1) for n in range(1,5))
    vprime = 1-sum((2*n-1)*(-1)**n*h[n]*z**(2*n) for n in range(1,5))
    amplitude = sp.series(vprime*sp.exp(-a*shift),z,0,7).removeO().expand()
    dj = [sp.factor(amplitude.coeff(z,j)) for j in range(7)]
    # Gamma-expectation all-order algorithm to order b^-2.
    # Work in z=1/b; factorial moments are exact polynomials.
    def moment(k, shift):
        return sp.expand(sum(sp.binomial(k,l)*(-1)**(k-l)
               *sp.prod(1+(shift+r)*z for r in range(l))
               for l in range(k+1)))
    v = sp.symbols('v')
    f = 1/(1+v**2)
    def expectation(shift):
        out = 0
        for k in range(7):
            out += sp.diff(f,v,k).subs(v,1)/sp.factorial(k)*moment(k,shift)
        return sp.series(out,z,0,3).removeO().expand()
    logst = sum((-1)**(r+1)*sp.bernoulli(r+1,d)/(r*(r+1))*z**r
                for r in range(1,3))
    st = sp.series(sp.exp(logst),z,0,3).removeO()
    total = 0
    for j in range(3):
        ratio = z**j/sp.prod(1+(d-r)*z for r in range(1,j+1))
        total += dj[j]*a**j*ratio*expectation(d-j)
    out = sp.series(2*st*total,z,0,3).removeO().expand()
    sigma=sp.symbols('sigma')
    B1 = sp.factor(out.coeff(z,1).subs({d:2*sigma,a:2*sp.pi})/(2*sp.pi))
    B2 = sp.factor(out.coeff(z,2).subs({d:2*sigma,a:2*sp.pi})/(2*sp.pi)**2)
    expected = (2*sigma**2-3*sigma+sp.Rational(7,12))/(2*sp.pi)-sp.pi/12
    assert sp.simplify(B1-expected)==0
    return {'exact_h': [str(x) for x in h[1:]],
            'density_coefficients_a': [str(x) for x in dj],
            'B1': str(B1), 'B2': str(B2),
            'B2_latex': sp.latex(sp.expand(B2)),
            'residual_order_checked': 8,
            'first_coefficients_match':True}

def strnum(x, n=40):
    return mp.nstr(x,n)

def run(dps: int = 240) -> dict:
    if dps < 180:
        raise ValueError('At least 180 decimal digits are required for this test grid.')
    mp.mp.dps=dps
    DATA.mkdir(exist_ok=True)
    sym = symbolic_checks()
    xvalues = [3,5,8,10,15,20,30,40]
    nmax = int(mp.floor(mp.pi*max(xvalues)))+4
    c,h=mp_coefficients(nmax)
    # Compare the independent exact and high-precision coefficient calculations.
    ce,he=exact_coefficients(14)
    for j in range(1,15):
        ref=mp.mpf(str(sp.numer(he[j])))/mp.mpf(str(sp.denom(he[j])))
        assert abs((h[j]-ref)/ref)<mp.power(10,-min(200,dps-20))
    rows=[]
    sigsym=sp.symbols('sigma')
    b2fun=sp.lambdify(sigsym,sp.sympify(sym['B2']),modules='mpmath')
    for xx in xvalues:
        x=mp.mpf(xx); w=inverse(x)
        for offset in (-1,0,1):
            m=int(mp.floor(mp.pi*x))+offset
            sigma=m+1-mp.pi*x
            s=x+mp.fsum(h[j]*x**(1-2*j) for j in range(1,m+1))
            u=forward_inverse(x,m,c)
            scale=(-1)**m*mp.sqrt(x)*mp.exp(-2*mp.pi*x)
            ratio=(s-w)/scale
            b1=(2*sigma**2-3*sigma+mp.mpf(7)/12)/(2*mp.pi)-mp.pi/12
            b2=b2fun(sigma)
            diffratio=(s-u)/((-1)**(m+1)*mp.pi/(6*mp.sqrt(x))*mp.exp(-2*mp.pi*x))
            row={'X':xx,'M':m,'offset':offset,'sigma':strnum(sigma),
                 'direct_ratio':strnum(ratio),
                 'prediction_1':strnum(1+b1/x),
                 'prediction_2':strnum(1+b1/x+b2/x**2),
                 'X2_residual_after_B1':strnum(x**2*(ratio-1-b1/x)),
                 'B2':strnum(b2),
                 'forward_ratio':strnum((u-w)/scale),
                 'direct_minus_forward_ratio':strnum(diffratio),
                 'direct_error':strnum(s-w), 'inverse':strnum(w)}
            assert (s-w)/((-1)**m)>0
            rows.append(row)
        print('direct remainder checked at X =',xx,flush=True)
    densities=[]
    for tt in (2,3,5,8,10,15,20,30,40):
        t=mp.mpf(tt)
        w=inverse(mp.j*t)
        rho=-mp.re(w)
        v=mp.findroot(lambda vv: mp.re(mp.digamma(mp.mpf('0.5')+mp.j*vv))-mp.log(t),
                      (t,t+1/(24*t)))
        Aprime=-mp.im(mp.polygamma(1,mp.mpf('0.5')+mp.j*v))
        linear=mp.pi/Aprime*mp.exp(-2*mp.pi*v)
        norm=mp.pi*t*mp.exp(-2*mp.pi*t)
        ratio=rho/norm
        d1=-mp.pi/12; d2=mp.pi**2/288-mp.mpf(1)/24
        densities.append({'t':tt,'rho':strnum(rho),'density_ratio':strnum(ratio),
            'prediction_2':strnum(1+d1/t+d2/t**2),
            'linearized_ratio':strnum(rho/linear),
            'root_residual':strnum(abs(mp.digamma(w+mp.mpf('0.5'))-mp.log(mp.j*t)))})
        assert rho>0
    # Existing late-coefficient equivalent, independently recovered by the spectral theorem.
    late=[]
    for n in (10,20,40,80,120):
        leading=2*(-1)**n*mp.gamma(2*n)/(2*mp.pi)**(2*n)
        late.append({'n':n,'ratio':strnum(h[n]/leading)})
    result={'precision_decimal_digits':dps,'python':platform.python_version(),
            'mpmath':mp.__version__,'sympy':sp.__version__,
            'symbolic':sym,'direct_remainders':rows,'densities':densities,
            'late_coefficient_comparison':late,
            'status':'All asserted finite checks passed; not interval arithmetic.'}
    # ed. (2026-09-29): LF line endings on every platform, like the filed files.
    (DATA/'results.json').write_text(json.dumps(result,indent=2)+'\n',newline='\n')
    for name,items in [('direct_remainders',rows),('density',densities),('late_coefficients',late)]:
        with (DATA/(name+'.csv')).open('w',newline='') as f:
            writer=csv.DictWriter(f,fieldnames=list(items[0]),lineterminator='\n'); writer.writeheader();writer.writerows(items)
    table=['\\begin{tabular}{rrrrr}','\\toprule',
           '$X$ & $M$ & Direct ratio & Two-correction prediction & Difference ratio \\\\',
           '\\midrule']
    for row in rows:
        if row['offset']==0:
            table.append(f"{row['X']} & {row['M']} & {float(row['direct_ratio']):.9f} & "
                         f"{float(row['prediction_2']):.9f} & {float(row['direct_minus_forward_ratio']):.9f} \\\\")
    table+=['\\bottomrule','\\end{tabular}']
    (DATA/'direct_table.tex').write_text('\n'.join(table)+'\n',newline='\n')
    print(json.dumps(sym,indent=2),flush=True)
    return result

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--dps',type=int,default=240)
    args=parser.parse_args()
    run(args.dps)
