"""Verify the formal inverse-logarithmic expansion using exact SymPy algebra.

The divergent series B is used only through finite polynomial truncations.
This checks algebra, not the analytic remainder estimates in the article.
"""
from pathlib import Path
import json
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
u, z, w = sp.symbols('u z w')

def trunc(expr, order):
    return sp.series(expr, u, 0, order+1).removeO().expand()

def main():
    n = 4
    B = sum(sp.rf(sp.Rational(3,2), j)*w**j for j in range(n+1))
    logB = sp.series(sp.log(B), w, 0, n+1).removeO().expand()
    polys = []
    T = 1+z*u
    for j in range(1,n+1):
        # Expand log B by its known coefficients, avoiding nested log expansion.
        invT = trunc(1/T, j)
        expr = trunc(sp.log(T),j)
        for h in range(1,j+1):
            expr -= logB.coeff(w,h)*u**h*trunc(invT**h,j-h)
        p = sp.expand(expr).coeff(u,j).expand()
        polys.append(p)
        T += p*u**(j+1)
    residual = sum(polys[j-1]*u**j for j in range(1,n+1)) - trunc(sp.log(T),n)
    invT = trunc(1/T,n)
    for h in range(1,n+1):
        residual += logB.coeff(w,h)*u**h*trunc(invT**h,n-h)
    residual = trunc(residual,n)
    assert residual == 0
    expected = [z-sp.Rational(3,2), -z**2/2+5*z/2-sp.Rational(33,8),
                z**3/3-3*z**2+sp.Rational(43,4)*z-15]
    assert polys[:3] == expected
    report = {'arithmetic':'exact rational polynomial algebra',
              'logB_coefficients':[str(logB.coeff(w,j)) for j in range(1,n+1)],
              'P_polynomials':[str(p) for p in polys],
              'P_latex':[sp.latex(p) for p in polys],
              'residual_through_u_power': n,
              'residual':str(residual),
              'result':'PASS (formal coefficient identities only)'}
    (ROOT/'data'/'expansion_verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__ == '__main__':
    main()
