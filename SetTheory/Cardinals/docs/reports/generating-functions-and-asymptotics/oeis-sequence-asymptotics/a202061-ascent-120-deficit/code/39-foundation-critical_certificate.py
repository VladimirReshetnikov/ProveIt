import sympy as s
from mpmath import mp
u=s.symbols('u'); f=7*u**3+14*u**2-7*u-1
k=(-21*u**2+17*u+5)/29
mu=(1+u)/(1-u-k);rho=1/mu
z=k*(1-u-k)/((u-k)*(2*u+k));b=1-rho;t=1/z
Q=b*z/(b*z+rho);beta=rho/(b*z);eta=rho**2/(b*b*z)
W=((1-z)*Q-z)/rho
zeta=(b*b-rho*rho*t)**2/((b+rho*t)**2*z)

def rem(v):return s.rem(s.together(v).as_numer_denom()[0],f,u)
checks={
 'entropy stationary alpha':(u+k)**2*(1+u)*(1-u-k)-u*(u-k)*(2*u+k)**2,
 'entropy stationary kappa':(u+k)**2*(u-k)*(1-u-k)-k**3*(2*u+k),
 'growth cubic':mu**3-8*mu**2+5*mu+1,
 'tilt cubic':z**3-5*z**2+6*z-1,
 'jump quadratic':rho*t*(1-z)*Q**2+(b*(z-b)+rho*t*(rho-z))*Q+b*z,
 'double jump root':2*rho*t*(1-z)*Q+(b*(z-b)+rho*t*(rho-z)),
 'positive W equation':W*b*(1-eta*(1+W))-z*(1+beta)*(1+W),
 'mass identity':beta*Q-rho/(b*z+rho),
 'tilt W identity':W-(1+beta),
 'zero tilt derivative identity':eta*(2+beta)**2-1,
 'discriminant factor linear coefficient':2*(b-rho*t)*(rho*rho*t-b*b)-4*rho*t*b+(b*b-rho*rho*t)**2*(1/z+1/zeta),
}
for name,v in checks.items():
 assert rem(v)==0,name
 print('PASS',name)
mp.dps=70
a=mp.findroot(lambda a:7*a**3+14*a**2-7*a-1,mp.mpf('.51'))
subs=lambda p:mp.mpf(str(s.N(p.subs(u,str(a)),65)))
for name,v in [('alpha',u),('kappa',k),('mu',mu),('rho',rho),('z',z),('t',t),('Qstar',Q),('beta',beta),('eta',eta),('Wstar',W),('eta*(1+W)',eta*(1+W)),('macro_mass',beta*Q),('A(rho)_upper',1+rho*t/(b*(1-beta*Q)))]:print(name,mp.nstr(subs(v),55))
# Rational isolating interval sufficient for every claimed positivity.
lo=s.Rational(51000337,10**8);hi=s.Rational(51000339,10**8)
assert f.subs(u,lo)<0<f.subs(u,hi)
assert s.diff(f,u).subs(u,lo)>0
print('PASS alpha isolated in',lo,hi)
from fractions import Fraction as F
class I:
 def __init__(self,a,b=None):self.a=F(a);self.b=F(a if b is None else b)
 def __add__(self,y):return I(self.a+y.a,self.b+y.b)
 def __mul__(self,y):
  v=[self.a*y.a,self.a*y.b,self.b*y.a,self.b*y.b];return I(min(v),max(v))
 def inv(self):
  assert not self.a<=0<=self.b
  return I(1/self.b,1/self.a)
 def pow(self,n):
  if n<0:return self.inv().pow(-n)
  v=I(1)
  for _ in range(n):v=v*self
  return v
 def __repr__(self):return '['+str(float(self.a))+', '+str(float(self.b))+']'
def box(p):
 if p==u:return I(F(lo),F(hi))
 if p.is_Rational:return I(F(p))
 if p.is_Add:
  v=I(0)
  for t0 in p.args:v=v+box(t0)
  return v
 if p.is_Mul:
  v=I(1)
  for t0 in p.args:v=v*box(t0)
  return v
 if p.is_Pow and p.exp.is_Integer:return box(p.base).pow(int(p.exp))
 raise ValueError(p)
for name,p,lower,upper in [
 ('alpha',u,F(1,2),F(3,5)),('kappa',k,F(1,4),F(1,3)),
 ('alpha-kappa',u-k,0,1),('1-alpha-kappa',1-u-k,0,1),
 ('mu',mu,F(729,100),F(730,100)),('z',z,F(19,100),F(20,100)),
 ('Wstar',W,0,3),('positive pole margin',eta*(1+W),0,F(1,2)),
 ('macro mass',beta*Q,F(2,5),F(1,2)),('Qstar',Q,F(1,2),F(3,5)),('second z root',zeta,F(88,100),F(89,100)),('sqrt discriminant constant',b*b-rho*rho*t,0,1)]:
 v=box(p)
 assert v.a>lower and v.b<upper,(name,v)
 print('PASS exact rational interval:',name,v)
