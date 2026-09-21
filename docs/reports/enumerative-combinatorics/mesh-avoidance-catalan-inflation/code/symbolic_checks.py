#!/usr/bin/env python3
"""Optional symbolic identities and numerical asymptotics.
Requires SymPy and mpmath. The main verifier has no third-party dependencies.
"""
from __future__ import annotations
import json
from pathlib import Path
import sympy as s
import mpmath as mp
from verify import coeffs


def main() -> None:
    x = s.symbols('x')
    D = x**4-2*x**3-5*x**2-2*x+1
    P = x**4+4*x**3+11*x**2+10*x+3
    Q = x**2+5*x+3
    B = (1+x-x**2-s.sqrt(D))/(2*x)
    I = (1-x-x**2-s.sqrt(D))/(2*(1+x))
    H = (1+3*x+x**2-s.sqrt(D))/(4*x*(1+x))
    A = (P-Q*s.sqrt(D))/(8*x*(1+x)**2)
    residuals = {
        'B_quadratic': x*B**2-(1+x-x**2)*B+1+x,
        'I_from_B': I-(1-x-1/B),
        'I_quadratic': I-x**2-(x+x**2)*I-(1+x)*I**2,
        'H_from_I': H*(1-I)-1,
        'A_from_H': A-H-x*H**2,
        'A_quadratic': 4*x*(1+x)**2*A**2-P*A+(1+x)*(2*x**2+6*x+3),
        'D_factorization': D-(x*x-(1+2*s.sqrt(2))*x+1)*(x*x+(2*s.sqrt(2)-1)*x+1),
    }
    for label, r in residuals.items():
        assert s.simplify(r) == 0, label
    mp.mp.dps = 80
    rho = (1+2*mp.sqrt(2)-mp.sqrt(5+4*mp.sqrt(2)))/2
    growth = 1/rho
    d = lambda z: z**4-2*z**3-5*z**2-2*z+1
    delta = mp.sqrt(-rho*mp.diff(d,rho))
    K = (rho**2+5*rho+3)*delta/(16*mp.sqrt(mp.pi)*rho*(1+rho)**2)
    Hr = (1+3*rho+rho*rho)/(4*rho*(1+rho))
    prob_one_fixed = 2*rho*Hr/(1+2*rho*Hr)
    S = lambda z:(z*z+5*z+3)/(8*z*(1+z)**2)
    correction = mp.mpf(3)/8-mp.mpf(3)/2*(rho*rho*mp.diff(d,rho,2)/(4*delta**2)-rho*mp.diff(S,rho)/S(rho))
    _,_,_,a = coeffs(200)
    ratios = {str(n):mp.nstr(mp.mpf(a[n])/(K*growth**n/(mp.mpf(n)**mp.mpf('1.5'))),25)
              for n in (20,50,100,200)}
    result = {'symbolic_residuals':{k:'0' for k in residuals},
              'rho':mp.nstr(rho,65),'growth_constant':mp.nstr(growth,65),
              'leading_constant':mp.nstr(K,65),
              'relative_1_over_n_correction':mp.nstr(correction,65),
              'limiting_probability_of_one_fixed_point':mp.nstr(prob_one_fixed,65),
              'ratios_to_leading_asymptotic':ratios}
    path = Path(__file__).resolve().parents[1]/'data'/'symbolic_and_asymptotic_results.json'
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__ == '__main__':
    main()
