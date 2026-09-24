#!/usr/bin/env python3
"""Optional exact algebra certificates and high-precision asymptotic checks.

Companion to code/verify_records.py, and independent of
code/symbolic_checks.py: it certifies the two polynomial identities that
make the final algebraic step hand-checkable, and evaluates the asymptotic
constants to 90 digits.  Requires sympy and mpmath; the standard-library
checkers have no dependencies.
"""
from __future__ import annotations
import csv
import json
from pathlib import Path
import sympy as sp
import mpmath as mp
from verify_records import fast_coefficients


def main() -> None:
    outdir = Path(__file__).resolve().parents[1]/'data'
    outdir.mkdir(parents=True,exist_ok=True)
    x, y, r = sp.symbols('x y r')
    D = x**4-2*x**3-5*x**2-2*x+1
    P = x**4+4*x**3+11*x**2+10*x+3
    Q = x**2+5*x+3
    G = (1+x)*r**2+(x+x**2-1)*r+x**2
    root_expression = 1-x-x**2-2*(1+x)*r
    certificate1 = sp.div(sp.expand(root_expression**2-D),G,r)
    assert sp.expand(certificate1[1]) == 0
    numerator = sp.expand((P-Q*root_expression)*(1-r)**2
                         -8*x*(1+x)**2*(1-r+x))
    certificate2 = sp.div(numerator,G,r)
    assert sp.expand(certificate2[1]) == 0
    I = r
    inflated = sp.factor((1+x*y)**2*(I**2 + (x*(1+y/(1+x*y))-1)*I
                                    +x**2*y/(1+x*y)))
    target = (1+x*y)*((1+x*y)*r**2+(x+x**2*y-1)*r+x**2*y)
    assert sp.expand(inflated-target) == 0
    a_symbol = sp.symbols('A')
    Apoly = sp.factor(((8*x*(1+x)**2*a_symbol-P)**2-Q**2*D)/(16*x*(1+x)**2))
    certificates = {
        'sqrt_certificate_quotient':str(sp.factor(certificate1[0])),
        'gf_certificate_quotient':str(sp.factor(certificate2[0])),
        'quadratic_for_A':str(Apoly),
        'status':'PASS', 'sympy_version':sp.__version__, 'mpmath_version':mp.__version__
    }
    (outdir/'symbolic_certificates.json').write_text(json.dumps(certificates,indent=2)+'\n')
    mp.mp.dps = 90
    alpha = (1+2*mp.sqrt(2)+mp.sqrt(5+4*mp.sqrt(2)))/2
    rho = 1/alpha
    D1 = lambda z: 4*z**3-6*z**2-10*z-2
    D2 = lambda z: 12*z**2-12*z-10
    B = lambda z: (z*z+5*z+3)/(8*z*(1+z)**2)
    K = B(rho)*mp.sqrt(-rho*D1(rho))/(2*mp.sqrt(mp.pi))
    c1 = mp.mpf(3)/8+3*rho*mp.diff(B,rho)/(2*B(rho))+3*rho*D2(rho)/(8*D1(rho))
    R0 = (1-rho-rho*rho)/(2*(1+rho))
    singleton_limit = 2*rho/(1-R0+2*rho)
    constants = {name:mp.nstr(value,75) for name,value in
                 [('alpha',alpha),('rho',rho),('K',K),('c1',c1),('R_rho',R0),
                  ('singleton_limit',singleton_limit)]}
    (outdir/'asymptotic_constants.json').write_text(json.dumps(constants,indent=2)+'\n')
    a = fast_coefficients(1000)
    with (outdir/'asymptotic_ratios.csv').open('w',newline='') as stream:
        writer = csv.writer(stream)
        writer.writerow(['n','a_n_over_leading_asymptotic','n_times_ratio_minus_one',
                         'a_n_over_two_term_asymptotic'])
        for n in [10,25,50,100,250,500,1000]:
            ratio = mp.mpf(a[n])/(K*alpha**n/mp.mpf(n)**mp.mpf('1.5'))
            writer.writerow([n,mp.nstr(ratio,30),mp.nstr(n*(ratio-1),30),
                             mp.nstr(ratio/(1+c1/n),30)])
    print(json.dumps(certificates,indent=2))
    print(json.dumps(constants,indent=2))
    print((outdir/'asymptotic_ratios.csv').read_text())


if __name__ == '__main__':
    main()
