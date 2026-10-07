#!/usr/bin/env python3
"""Exact direct-U Laurent certificate. Optional dependency: SymPy."""
import argparse
from pathlib import Path
from output_json import emit_json, prepare_output

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=Path)
args=parser.parse_args()
prepare_output(parser,args.output)
# Reject unsafe output paths before loading the optional dependency.
try:
 import sympy as S
except ImportError as error:
 raise SystemExit("check_poles.py requires the optional sympy package") from error
def require(condition):
 if not condition:raise ValueError('Symbolic identity failed')
s,b,tau,p,A,C,D,eta,Epp=S.symbols('s beta tau rho a0 c0 d20 eta Epp',nonzero=True)
z=p*(1-s*s)
t4=b**4/S.Integer(45)-2*b*tau/3
t=b*s-b*b*s*s/3+tau*s**3+t4*s**4
# Derive tau from the implicit rooted-tree equation at even order four.
phi=sum(t**j/S.Integer(j) for j in range(2,6))
tau_eq=S.expand(phi).coeff(s,4)-(1-p*p*Epp)/2
tau_value=S.solve(tau_eq,tau)[0]
require(S.simplify(tau_value-(b**3/36+(1-p*p*Epp)/(2*b)))==0)
require(S.expand(phi).coeff(s,5)==0)
# Direct closed formula simplification, using the BASELINE positive B expression.
g,az,cz,dz2,dz3,zz=S.symbols('g a c d2 d3 z')
r=1-1/g;d=az*g;f=(1-zz)*d
h=(1-zz)*az;j2=(1-zz)*(1-zz**2)*cz
f2=(1-zz**2)*dz2
B=zz*j2*g/(1-zz)+(1+zz)*f*f/(1-zz)+zz*r*g*((f*f-f2)/2+zz*f*f/(1-zz))
e2=(d*d-dz2)/2;e3=(d**3-3*d*dz2+2*dz3)/6
Y=S.factor(g*(cz*d+(az+zz*r*d)*B/(1-zz**2)+az*e2+zz**2*r*e3))
Ysimple=(az**3*(zz**2*g**5/2+zz*(9-5*zz)*g**4/6+(2*zz**2-9*zz+9)*g**3/6)
 +az*cz*(zz**2*g**3+(1+zz-zz**2)*g**2)
 -az*dz2*(zz**2*g**3+zz*(1-zz)*g**2+(1-zz)*g)/2
 +zz**2*dz3*(g-1)/3)
require(S.factor(Y-Ysimple)==0)
# Polynomial-ring coefficient convolution keeps this inexpensive and exact.
def coeffs(expr,degree):return [S.expand(S.series(expr,s,0,degree+1).removeO()).coeff(s,i) for i in range(degree+1)]
def conv(a,c,n=3):return [S.expand(sum(a[j]*c[i-j] for j in range(i+1))) for i in range(n+1)]
def powser(a,q,n=3):
 out=[S.Integer(1)]+[S.Integer(0)]*n
 for _ in range(q):out=conv(out,a,n)
 return out
# g=s^-1*gnorm; a=Aanalytic*exp(-t/z), c=Canalytic*exp(-t/z²).
gnorm=[1/b,S.Rational(1,3),b/9-tau/b**2,2*b*b/S.Integer(135)]
for expected,actual in zip(gnorm,coeffs(s/t,3)):
 require(S.simplify(expected-actual)==0)
a=coeffs(A*(1+eta*s*s)*S.exp(-t/z),3)
c=coeffs(C*S.exp(-t/z**2),3)
d2=[D,0,0,0]
blocks=[
 ('cubic5',conv(powser(a,3),coeffs(z*z/2,3)),5),
 ('cubic4',conv(powser(a,3),coeffs(z*(9-5*z)/6,3)),4),
 ('cubic3',conv(powser(a,3),coeffs((2*z*z-9*z+9)/6,3)),3),
 ('ac3',conv(conv(a,c),coeffs(z*z,3)),3),
 ('ac2',conv(conv(a,c),coeffs(1+z-z*z,3)),2),
 ('ad3',conv(conv(a,d2),coeffs(-z*z/2,3)),3),
 ('ad2',conv(conv(a,d2),coeffs(-z*(1-z)/2,3)),2),
]
poles={j:S.Integer(0) for j in [-5,-4,-3,-2]}
groups={name:{j:S.Integer(0) for j in [-4,-2]} for name in ['cubic','ac','ad']}
for name,numer,q in blocks:
 block=conv(numer,powser(gnorm,q))
 for j in poles:
  if 0<=j+q<=3:
   poles[j]+=block[j+q]
   if j in [-4,-2]:groups['cubic' if name.startswith('cubic') else name[:2]][j]+=block[j+q]
poles={j:S.factor(v) for j,v in poles.items()}
require(poles[-4]==0 and poles[-2]==0)
for group in groups.values():
 for value in group.values():
  require(S.factor(value)==0)
require(S.factor(poles[-5]-p*p*A**3/(2*b**5))==0)
# Multiply by (1-z³), whose second coefficient can mix only -5 into -3.
u5=S.factor((1-p**3)*poles[-5])
u3=S.factor((1-p**3)*poles[-3]+3*p**3*poles[-5])
M=S.Rational(3,2)*eta+b*b*(S.Rational(1,18)+1/p-3/(4*p*p))-5*tau/(2*b)
h3=A**3*M/b**5+A*(C-D/2)/b**3
u3_proposed=p*p*(1-p**3)*h3+(-2*p*p+5*p**5)*A**3/(2*b**5)
require(S.factor(u3-u3_proposed)==0)
out={'status':'direct-U algebra and all pole checks pass','tau':str(tau_value),'Y_poles':{str(j):str(v) for j,v in poles.items()},'U_minus5':str(u5),'U_minus4':'0','U_minus2':'0','U_minus3_identity_verified':True,'groupwise_even_pole_cancellations':True,'inverse_G_jet_verified':True,'implicit_odd_coefficient_verified':True}
emit_json(parser,out,args.output)
