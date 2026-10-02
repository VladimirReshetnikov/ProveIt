"""Exact rational checks of degree-two carriers and formal inverse coefficients."""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import importlib.util,json
import sympy as S
ROOT=Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('cyclic',ROOT/'fixed/cyclic_covers.py');cyc=importlib.util.module_from_spec(sp);sp.loader.exec_module(cyc)
def degree2(K,s):
    out=[F(0)]*(K+1)
    for b in range(K+1):
        m=K-b;p=[F(1)]+[F(0)]*m
        for denom,ct in [(3,3*b),(2,2*b)]:
            for i in range(ct):p=cyc.conv(p,[F(1),F(-i,denom)],m)
        for i in range(6*b):p=cyc.conv(p,[F(i,6)**j for j in range(m+1)],m)
        for j in range(m+1):out[b+j]+=F(s,36)**b/factorial(b)*p[j]
    return out
z=S.symbols('z');ds={}
for s in [1,-1]:
    cs=cyc.coeffs(3,s)
    log=S.series(S.log(sum(S.Rational(c.numerator,c.denominator)*z**k for k,c in enumerate(cs))),z,0,4).removeO()-z/18+S.Rational(13,4860)*z**3
    got=[S.expand(log).coeff(z,k) for k in range(1,4)]
    want=[S.Rational(5,6),S.Rational(8,9),S.Rational(4013,4860)] if s==1 else [S.Rational(-1,18),S.Integer(0),S.Rational(-307,4860)]
    assert got==want
    ds[str(s)]=list(map(str,got))
a,D,d1,d2,d3=S.symbols('a D d1 d2 d3',nonzero=True)
delta=-d1*z/D-d2*z**2/D-(d3/D+d1**2/D**2+a*d1**2/(2*D**3))*z**3
res=D*delta+a*z*delta**2/2+d1*z/(1+z*delta)+d2*z**2/(1+z*delta)**2+d3*z**3/(1+z*delta)**3
assert S.series(res,z,0,4).removeO().expand()==0
out={'degree_two_coefficients_relative_to_D':{str(s):list(map(str,degree2(5,s))) for s in [1,-1]},'cubic_log_coefficients_d1_d2_d3':ds,'inverse_reversion_residual_through_order_three':'0'}
assert degree2(1,1)[1]==F(1,36) and degree2(1,-1)[1]==F(-1,36)
(ROOT.parent/'results/degree-two-inverse-results.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: degree-two first corrections, cubic logarithmic coefficients and inverse Taylor reversion')
