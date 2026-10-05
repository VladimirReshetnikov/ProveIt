"""Exact low-alphabet checks of the general all-orders coefficient rule."""
from pathlib import Path
from math import factorial
import json,sympy as s
e,G,u,x=s.symbols('e G u x');rows=[]

def gaussian(poly,var):
    out=0
    for (j,),a in s.Poly(s.expand(poly),G).terms():
        if j%2==0:out+=a*s.factorial(j)/s.factorial(j//2)/2**(j//2)*var**(j//2)
    return s.simplify(out)
for r in (2,3):
    if r==2:
        t=(1-x*x)/2
        E=(1-s.sqrt(1-4*t*t))/(2*t*t)
        ex=s.series(E,x,0,6).removeO().expand()
        p1,p3,p5=[s.simplify(ex.coeff(x,j)) for j in (1,3,5)]
        B1=s.Rational(3,8)-s.Rational(3,2)*p3/p1
        B2=s.Rational(25,128)-s.Rational(45,16)*p3/p1+s.Rational(15,4)*p5/p1
        c1=s.simplify(B1/2);c2=s.simplify(B2/4)
        expected=(s.Rational(-9,8),s.Rational(145,128))
    else:
        # All three letters remain marked; u marks the zero step.
        p3over1=(u+14)/8
        p5over1=3+(u-2)/4-(u-2)**2/128
        B1=s.Rational(3,8)-s.Rational(3,2)*p3over1
        B2=s.Rational(25,128)-s.Rational(45,16)*p3over1+s.Rational(15,4)*p5over1
        phase=s.series(s.log(s.exp(e*G)+2)-e*G/3,e,0,7).removeO().expand()
        phasecorr=sum(s.I**j*phase.coeff(e,j)*e**(j-2) for j in range(3,7))
        amp=s.series(((s.exp(s.I*e*G)+2)/3)**s.Rational(3,2),e,0,5).removeO()
        transfer=1+e*e*B1.subs(u,s.exp(s.I*e*G))+e**4*B2.subs(u,1)
        expr=s.series(amp*transfer*s.series(s.exp(phasecorr),e,0,5).removeO(),e,0,5).removeO().expand()
        c1=s.simplify(gaussian(expr.coeff(e,2),s.Rational(9,2))/3)
        c2=s.simplify(gaussian(expr.coeff(e,4),s.Rational(9,2))/9)
        expected=(s.Rational(-11,9),s.Rational(101,81))
    if (c1,c2)!=expected:raise RuntimeError(('recipe',r,c1,c2,expected))
    rows.append({'r':r,'c1':str(c1),'c2':str(c2)})

# The general two-correction Lambert-core inverse, with alpha arbitrary.
z,c,A,b1,b2=s.symbols('z c A b1 b2',nonzero=True)
delta=-b1*z/(c-A*z)-b2*z*z/(c-A*z)
res=c*delta-A*s.log(1+z*delta)+b1*z/(1+z*delta)+b2*z*z/(1+z*delta)**2
if s.simplify(s.series(res,z,0,3).removeO())!=0:raise RuntimeError('general inverse')
out={'passed':True,'general_inverse_passed':True,'records':rows,'method':'Direct Catalan/Motzkin marked kernels and Gaussian integration'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
