#!/usr/bin/env python3
"""Independent diagnostic checks of the endpoint Gram and primitive formulas.

Numerical comparisons are not interval certificates. The exact determinant
calculation uses SymPy and is separate from those comparisons.
"""
import argparse
import json
from pathlib import Path
import mpmath as mp
import sympy as sy
from verify_translation import coefficients, variance_hurwitz, variance_tail_bound


def kernel(s,t):
    u=s+t
    return (mp.gamma(1-s)*mp.gamma(1-t)/mp.gamma(2-u)
            *mp.cos(mp.pi*(s-t)/2)/mp.cos(mp.pi*u/2))


def power_increment(s,x):
    return x**(-s)*mp.expm1(-s*mp.log1p(1/x))


def polynomial_increment(r,ell,x):
    base=ell-mp.log(x)
    delta=-mp.log1p(1/x)
    return mp.fsum(mp.binomial(r,j)*base**(r-j)*delta**j
                   for j in range(1,r+1))


def primitive(h):
    w=[mp.zeta(-2,h,derivative=j)-mp.zeta(-2,1-h,derivative=j)
       for j in range(3)]
    a=2+mp.pi**2/3
    q=mp.zeta(-1,derivative=2)+2*mp.zeta(-1,derivative=1)+a*mp.zeta(-1)
    return w[2]/2+3*w[1]/2+(mp.mpf(7)/4+mp.pi**2/6)*w[0]-2*h*q


def primitive_series(h,coeff):
    ell=mp.log(1/h)
    return (h*h/2*(ell*ell+3*ell+mp.mpf(7)/2+mp.pi**2/3)
            +(2*mp.stieltjes(1)-mp.pi**2/3)*h**3/3
            -mp.fsum(2*b*h**(2*j+1)/(j*(2*j-1)*(2*j+1)) for j,b in coeff))


def run():
    mp.mp.dps=70
    records=[]
    def check(label,left,right,tolerance=mp.mpf('1e-44')):
        error=abs(left-right)
        row=dict(label=label,error=mp.nstr(error,14),tolerance=mp.nstr(tolerance,14),
                 passed=bool(error<tolerance))
        records.append(row)
        print(label,'PASS' if row['passed'] else 'FAIL',row['error'],flush=True)
    for s,t in [(mp.mpf('.11'),mp.mpf('.13')),
                (mp.mpc('-.12','.06'),mp.mpc('.04','-.03'))]:
        val=1/(1-s-t)+mp.quad(lambda x:power_increment(s,x)*power_increment(t,x),
                              [0,mp.mpf('.2'),1,5,mp.inf])
        check('power-increment kernel '+str((s,t)),val,kernel(s,t))
    ell=mp.mpf('.7')
    value=(mp.quad(lambda x:(ell-mp.log(x))**4,[0,1])
           +mp.quad(lambda x:polynomial_increment(2,ell,x)**2,[0,1,5,mp.inf]))
    expected=(ell**4+4*ell**3+(12+4*mp.pi**2/3)*ell**2
              +(24+8*mp.pi**2/3-8*mp.zeta(3))*ell
              +24+8*mp.pi**2/3-8*mp.zeta(3)+7*mp.pi**4/45)
    check('P22 Gram integral',value,expected)
    h=mp.mpf('.3')
    coeff=coefficients(50)
    check('Gamma definite primitive vs integrated convergent series',primitive(h),
          primitive_series(h,coeff),h*variance_tail_bound(h,50)+mp.mpf('1e-55'))
    for m in [1,2]:
        def dgamma(a):
            return ((-1)**(m+1)*mp.factorial(m)*mp.zeta(m+1,a,derivative=1)
                    +mp.harmonic(m)*mp.polygamma(m,a))
        expected=2*(dgamma(h)+(-1)**m*dgamma(1-h))
        check('Gamma derivative order '+str(m+2),mp.diff(variance_hurwitz,h,m+2),expected)

    # Exact polynomial congruence/determinant, independent of floating checks.
    L=sy.symbols('L')
    p=sy.pi**2/3
    mat=sy.Matrix([[1,L+1,L**2+2*L+2],
                   [L+1,L**2+2*L+2+p,
                    L**3+3*L**2+(6+2*p)*L+6+2*p-2*sy.zeta(3)],
                   [L**2+2*L+2,L**3+3*L**2+(6+2*p)*L+6+2*p-2*sy.zeta(3),
                    L**4+4*L**3+(12+4*p)*L**2+(24+8*p-8*sy.zeta(3))*L
                    +24+8*p-8*sy.zeta(3)+7*sy.pi**4/45]])
    triangular=sy.Matrix([[1,0,0],[L,1,0],[L**2,2*L,1]])
    assert (mat-triangular*mat.subs(L,0)*triangular.T).applyfunc(sy.expand)==sy.zeros(3)
    determinant=sy.factor(mat.det())
    assert sy.diff(determinant,L)==0
    print('Exact P2 binomial congruence and determinant PASS',flush=True)
    return dict(proof_status='numerical diagnostics plus exact symbolic determinant',dps=70,
                records=records,all_passed=all(r['passed'] for r in records),
                exact_P2_determinant=str(determinant),exact_congruence_passed=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'verification'/'translation_extensions.json')
    args=parser.parse_args()
    result=run()
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    if not result['all_passed']:raise SystemExit(1)
