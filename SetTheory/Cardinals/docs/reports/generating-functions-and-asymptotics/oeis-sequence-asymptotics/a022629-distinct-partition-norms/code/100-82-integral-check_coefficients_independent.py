"""Independent exact low-order checks for the A022629 saddle proof."""
import json
from pathlib import Path
import sympy as s
z,b=s.symbols('z b')
c,d=s.symbols('c d')
A=b/2-1+c/(b-1)+d*(2*b+1)/(b-1)**5
# Solve directly for lambda=K/sqrt(2n), rather than a logarithmic shift.
lambda_series=s.Integer(1)
for j in range(2,6):
    x=s.Symbol('l'+str(j)); trial=lambda_series+x*z**j
    bj=1/z+s.series(s.log(trial),z,0,7).removeO()
    ratio=2*(A+s.diff(A,b))/(b-1)
    equation=s.series(trial**2*ratio.subs(b,bj)-1,z,0,j+1).removeO().expand().coeff(z,j)
    value=s.solve(equation,x)[0]
    lambda_series+=value*z**j
bj=1/z+s.series(s.log(lambda_series),z,0,7).removeO()
phase=s.series(lambda_series*A.subs(b,bj)+bj/(2*lambda_series),z,0,5).removeO().expand()
expected=1/z-1+c*z+c*z**2+(c-c**2/2)*z**3+(c-c**2/2+2*d)*z**4
if s.simplify(phase-expected)!=0: raise RuntimeError(('forward',phase,expected))
# Independently revert in the direct multiplicative X/X0 variable.
r=s.Integer(1)
for j in range(2,5):
    x=s.Symbol('r'+str(j));trial=r+x*z**j
    bj=1/z+s.series(s.log(trial),z,0,6).removeO()
    loggrowth=bj-1+c/bj+c/bj**2+(c-c**2/2)/bj**3
    eq=s.series(trial*loggrowth-(1/z-1),z,0,j).removeO().expand().coeff(z,j-1)
    r+=s.solve(eq,x)[0]*z**j
inverse=s.series(r*r,z,0,5).removeO().expand()
expected_inverse=1-2*c*z**2-2*c*z**3+(4*c*c-2*c)*z**4
if s.simplify(inverse-expected_inverse)!=0: raise RuntimeError(('inverse',inverse))
# Check the edge Jacobian derivatives and exact spatial second derivative.
D=lambda f:s.cancel(b*s.diff(f,b)/(b-1))
if s.simplify(D(D(D(b)))/b-(2*b+1)/(b-1)**5)!=0: raise RuntimeError('edge recurrence')
x,t=s.symbols('x t',positive=True)
p=x*s.exp(-t*x)/(1+x*s.exp(-t*x))
f=s.log(1+x*s.exp(-t*x))
check=s.diff(f,x,2)+p*p/x**2+2*t*p*(1-p)/x-t*t*p*(1-p)
if s.simplify(check)!=0: raise RuntimeError('spatial derivative')
result={'status':'PASS','forward_through_B_inverse_power':4,'inverse_through_C_inverse_power':4,'forward':str(phase),'inverse':str(inverse),'lambda_series':str(lambda_series),'independent_method':'Direct multiplicative saddle and inverse reversion; no imported producer code.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
