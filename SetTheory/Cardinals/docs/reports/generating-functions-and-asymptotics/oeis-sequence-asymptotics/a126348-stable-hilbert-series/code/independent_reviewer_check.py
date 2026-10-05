"""Independent reconstruction from the small-fugacity modular core and Gaussian polynomials."""
import json
from pathlib import Path
import sympy as s
z,L=s.symbols('z L');c=s.pi**2/6
order=6
def tr(f,n=order+2):return s.series(f,z,0,n).removeO().expand()
delta=tr(1-s.exp(-z),order+3)
shift=tr(-s.log(delta/z),order+3)
G=0
for j in range(1,order+2):
    G+=tr((-1)**(j+1)*delta**j/(j*(1-s.exp(-j*z))),order+1)
core=tr(((L+shift)**2-L**2)/(2*z)-(L+shift)/2+z/12-G,order+1)
expected=[(5-L)/24,-s.Rational(1,9),(2*L+245)/5760,-s.Rational(11,900),-(8*L+2037)/1451520,s.Rational(341,52920)]
if s.simplify(core.coeff(z,0)+1):raise RuntimeError('constant')
for j,p in enumerate(expected,1):
    if s.simplify(core.coeff(z,j)-p):raise RuntimeError(('P',j,core.coeff(z,j)))
# Build exponent coefficients through epsilon^4 directly, then use the
# exponential coefficient recurrence, rather than expanding exp(Q+R).
x,V=s.symbols('x V',positive=True)
v3,v4,v5,v6=s.symbols('v3 v4 v5 v6')
p1=(5-L)/24;p2=-s.Rational(1,9)
a={1:-s.I*v3*x**3/(6*V**s.Rational(3,2)),2:v4*x**4/(24*V**2)+p1,3:s.I*v5*x**5/(120*V**s.Rational(5,2))-s.I*x*(p1-s.diff(p1,L))/s.sqrt(V),4:-v6*x**6/(720*V**3)+p2+s.diff(p1,L)*x**2/(2*V)}
b={0:s.Integer(1)}
for n in range(1,5):b[n]=s.expand(sum(k*a[k]*b[n-k] for k in range(1,n+1))/n)
def gaussian(poly):
    result=0
    for (degree,),v in s.Poly(poly,x).terms():
        if degree%2==0:result+=v*(s.factorial2(degree-1) if degree else 1)
    return s.factor(result)
c1=gaussian(b[2]);c2=gaussian(b[4])
e1=v4/(8*V**2)-5*v3**2/(24*V**3)
e2=-v6/(48*V**3)+7*v3*v5/(48*V**4)+35*v4**2/(384*V**4)-35*v3**2*v4/(64*V**5)+385*v3**4/(1152*V**6)
if s.simplify(c1-p1-e1):raise RuntimeError('C1')
if s.simplify(c2-(p2+p1*p1/2+p1*e1+e2-1/(48*V)-(6-L)*v3/(48*V**2))):raise RuntimeError('C2')
A=L**2/2+L+c;B=L**2+L+2*c;VV=L**2+3*L+2*c+1
if s.simplify(2*A+s.diff(A,L)-VV) or s.simplify(B+s.diff(B,L)-VV):raise RuntimeError('inverse carrier derivatives')
result={'status':'PASS','modular_log_coefficients':[str(p) for p in expected],'gaussian_coefficients_checked':2,'inverse_carrier_derivatives_checked':2,'method':'Independent small-fugacity core Taylor series and exponential coefficient recurrence; no imported producer code.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
