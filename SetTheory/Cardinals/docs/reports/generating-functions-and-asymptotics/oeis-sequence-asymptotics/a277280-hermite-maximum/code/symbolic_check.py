"""Optional exact symbolic check of the three displayed correction polynomials.
Run: python code/symbolic_check.py
Requires sympy. This checks algebra, not the analytic remainder proof.
"""
from pathlib import Path
import sympy as S

t,u,z=S.symbols('t u z', positive=True)
n=1/(2*t*t)
d=1/t+u
m=(n-d)/2

def stirling(x):
    return ((x+S.Rational(1,2))*S.log(x)-x+S.log(2*S.pi)/2
            +1/(12*x)-1/(360*x**3))

expansion=S.expand(S.series(stirling(n)-stirling(m)-stirling(d)+d*S.log(2),t,0,4).removeO())
main=-S.log(t)/(2*t*t)-1/(4*t*t)+1/t-S.Rational(1,2)-S.log(S.pi)/2+S.log(t)/2
expected=[S.Rational(41,24)-z*z/2,
          z**3/6-z*z+S.Rational(47,24)*z-S.Rational(3,4),
          -z**4/12+z**3/3-S.Rational(35,24)*z*z+S.Rational(47,12)*z-S.Rational(8719,2880)]
residual=S.expand((expansion-main).subs(u,z-S.Rational(3,2)))
for j,p in enumerate(expected,1):
    assert S.simplify(residual.coeff(t,j)-p)==0
text='PASS: exact symbolic coefficients agree.\n'+ '\n'.join(f'P{j} = {p}' for j,p in enumerate(expected,1))+'\n'
print(text)
(Path(__file__).resolve().parents[1]/'data'/'symbolic_check.txt').write_text(text)
