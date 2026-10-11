"""Exact symbolic certificates for the quartic digamma/harmonic bridge."""
import json
from pathlib import Path
import sympy as s
x,n,g,z2,z3,z4=s.symbols('x n gamma zeta2 zeta3 zeta4')
b,c,e,f=s.symbols('b c e f')
checks={}
def checked(name,expr):
 expr=s.cancel(s.expand(expr))
 assert expr==0,(name,expr)
 checks[name]=True
r=-4*b**3+12*b*c-4*e
d=6*b*b-4*c
series=s.expand((-1/x+b+c*x+e*x*x+f*x**3)**4)
for k,wanted in [(-4,1),(-3,-4*b),(-2,d),(-1,r),(0,b**4-12*b*b*c+6*c*c+12*b*e-4*f)]:
 checked('principal_coefficient_'+str(k),series.coeff(x,k)-wanted)
checked('residue_finite_difference',r.subs({b:b+1/n,c:c+1/n**2,e:e+1/n**3})-r-12*(c-b*b)/n-4/n**3)
X,Y,Z,W,S12,S13,S22,S112=s.symbols('X Y Z W S12 S13 S22 S112')
SR=(-X**4+4*g*X**3+(-6*g*g+6*z2)*X*X+(4*g**3-12*g*z2+4*z3)*X
    +6*X*X*Y-12*g*X*Y-4*X*Z+(-6*g*g+6*z2)*Y-16*g*Z-11*W
    +24*g*S12-12*S112+20*S13+6*S22)
prev={X:X-1/n,Y:Y-1/n**2,Z:Z-1/n**3,W:W-1/n**4,
      S12:S12-X/n**2,S13:S13-X/n**3,S22:S22-Y/n**2,S112:S112-X*X/n**2}
rn=r.subs({b:X-g,c:z2+Y,e:Z-z3})
checked('finite_sum_initial',SR.subs({X:0,Y:0,Z:0,W:0,S12:0,S13:0,S22:0,S112:0}))
checked('finite_sum_difference',SR-SR.subs(prev,simultaneous=True)-rn/n)
L=s.symbols('L')
def reduce4(expr):return s.expand(expr).subs(z2*z2,s.Rational(5,2)*z4)
C=g**4-18*g*g*z2+32*g*z3-s.Rational(23,2)*z4
lim=SR.subs({X:L+g,Y:z2,Z:z3,W:z4,S12:2*z3,S13:s.Rational(5,4)*z4,S22:s.Rational(7,4)*z4,S112:s.Rational(17,4)*z4})
checked('finite_sum_asymptotic_constant',reduce4(lim+L**4-12*z2*L*L-C))
Cstar=g**4-12*g*g*z2+12*g*z3+11*z4
P0_integral=-s.Rational(1,3)-2*g-6*g*g+4*z2
m4=s.Rational(1,3)-z4
m3=-2*(z3-g)+4*(s.Rational(5,4)*z4-g*z3)
Td2=6*s.Rational(17,4)*z4-12*g*2*z3+(6*g*g-4*z2)*z2-4*s.Rational(7,4)*z4
Tdt=6*g*g-4*z2+14*z3-12*g*z2
K=g**4-18*g*g*z2+32*g*z3+s.Rational(13,2)*z4+12*z3-12*g*z2
checked('integrated_higher_poles',reduce4(P0_integral+Cstar+m4+m3+Tdt-Td2-K))
checked('constant_difference',K-C-(18*z4+12*z3-12*g*z2))
g1,g3,eta,beta1,E,Zp3=s.symbols('gamma1 gamma3 eta beta1 E zeta_prime3')
Q=18*z4+12*z3-12*g*z2+4*Zp3+12*g3-24*z2*g1+12*E
E_expr=-2*beta1+2*g*eta+(g*g+z2)*g1-g3
final=18*z4+12*z3-12*g*z2+4*Zp3+12*(g*g-z2)*g1+24*g*eta-24*beta1
checked('Laurent_coefficient_conversion',Q.subs(E,E_expr)-final)
Q3=3*z2-6*eta-6*g*g1
checked('cubic_coordinate_elimination',final+4*g*Q3-(18*z4+12*z3+4*Zp3-12*(g*g+z2)*g1-24*beta1))
z=s.symbols('z')
primitive=(s.Rational(1,3)/n**3-s.Rational(1,3)/(n+z)**3-z/n**4
   -4*b*(s.Rational(1,2)/n**2-s.Rational(1,2)/(n+z)**2-z/n**3)
   +d*(1/n-1/(n+z)-z/n**2)+r*(s.log(1+z/n)-z/n))
Pn=1/(n+z)**4-4*b/(n+z)**3+d/(n+z)**2+r/(n+z)
checked('normalized_primitive_derivative',s.diff(primitive,z)-Pn+Pn.subs(z,0))
checked('normalized_primitive_origin',primitive.subs(z,0))
report={'exact_checks':len(checks),'all_passed':all(checks.values()),'checks':checks,'sympy_version':s.__version__}
p=Path(__file__).with_name('quartic_exact_results.json')
p.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
