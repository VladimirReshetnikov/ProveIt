"""High-precision diagnostics, NOT interval-certified proofs. mpmath required."""
from pathlib import Path
import json
from fractions import Fraction
import mpmath as mp
import sympy as sp
from normal_form import reduce,bell_next
HERE=Path(__file__).resolve().parent
mp.mp.dps=50
checks=[]
def check(name,lhs,rhs,tol='1e-38'):
 err=abs(lhs-rhs)/max(1,abs(lhs),abs(rhs))
 assert err<mp.mpf(tol),(name,lhs,rhs,err)
 checks.append({'name':name,'scaled_residual':mp.nstr(err,8),'tolerance':tol})
def E2(t):
 return mp.hyp1f1(1,3,t)/2

def base(y):
 if not y:return mp.mpf(1)
 return (mp.cosh(y)+mp.sinh(y)/y-y*mp.shi(y))/2

def full(y,z,w):
 h=lambda v:(1+3*v*v)/24
 k=lambda v:(v+v**3)/48
 return base(y)+z*z/384*mp.quad(lambda v:(1-v*v)**2*mp.exp(y*v)*E2(z*h(v)),[-1,0,1])-w*w/18432*mp.quad(lambda v:(1-v*v)**3*mp.exp(y*v+z*h(v))*E2(w*k(v)),[-1,0,1])
# Genuine independent normal-form truncation at small t.
Ps=[];P={():Fraction(1)}
for W in range(31):
 N,H=reduce(P);Ps.append(N);P=bell_next(P)
for i in range(8):
 t=mp.mpf('0.002')*(i+1)
 U=[mp.mpf('0.4'),mp.mpf('0.3'),mp.mpf('-0.2'),mp.mpf('0.1')]
 if i%2:U[1]+=mp.mpc(0,'0.1');U[2]+=mp.mpc(0,'0.04')
 val=0
 for W,N in enumerate(Ps):
  val+=t**W/mp.factorial(W)*sum(mp.mpf(c.numerator)/c.denominator*mp.fprod(U[j]**a for j,a in enumerate(m)) for m,c in N.items() if len(m)<=4)
 target=mp.exp(U[0]*t)*full(U[1]*t*t/2,U[2]*t**3,U[3]*t**4)
 check('normal projection vs compact integral '+str(i),val,target)

v=sp.symbols('v')
polys=[(1-v*v)**3,(1-v*v)**3*(1+3*v*v),(1-v*v)**3*(v+v**3)]
for i,p in enumerate(polys):
 f=sp.lambdify(v,p,'mpmath')
 val=mp.quad(lambda v:f(v)*mp.digamma(2+v),[-1,0,1])
 if i==0:rhs=16*mp.diff(mp.zeta,-3)+12*mp.diff(mp.zeta,-5)+mp.mpf(2)/7
 elif i==1:rhs=64*mp.diff(mp.zeta,-3)+240*mp.diff(mp.zeta,-5)+48*mp.diff(mp.zeta,-7)+mp.mpf(547)/1800
 else:rhs=mp.mpf(32)/105-84*mp.zeta(5)/mp.pi**4+mp.mpf(1575)*mp.zeta(7)/(2*mp.pi**6)-mp.mpf(2835)*mp.zeta(9)/(2*mp.pi**8)
 check('weighted digamma '+str(i),val,rhs)

for i,p in enumerate(polys):
 f=sp.lambdify(v,p,'mpmath');d=sp.degree(p,v)
 for ss in [mp.mpf('0.3'),mp.mpf('2.4'),mp.mpc('0.7','0.2')]:
  a=mp.mpf('2.3')
  lhs=mp.quad(lambda v:f(v)*mp.zeta(ss,a+v),[-1,0,1])/2
  rhs=0
  for j in range(d+1):
   A=int(sp.diff(p,v,j).subs(v,1));B=int(sp.diff(p,v,j).subs(v,-1))
   den=mp.fprod(ss-r for r in range(1,j+2))
   rhs-=(A*mp.zeta(ss-j-1,a+1)-B*mp.zeta(ss-j-1,a-1))/(2*den)
  check('Hurwitz endpoint '+str(i)+' '+str(ss),lhs,rhs)

# Polylogarithm summations from the mixed square coefficient density.
for b in range(3):
 p=sp.Poly((1-v*v)**3*(1+3*v*v)**b,v)
 ds={m[0]//2:int(c) for m,c in p.terms()}
 for m in [1,2,4]:
  z=mp.mpf('0.4')
  chi=lambda r:(mp.polylog(r,z)-mp.polylog(r,-z))/2
  lhs=mp.mpf(0)
  for ell in range(100):
   density=sum(mp.mpf(d)/(2*ell+2*j+1) for j,d in ds.items())
   lhs+=density*z**(2*ell+1)/(2*ell+1)**m
  rhs=0
  for j,d in ds.items():
   if j==0:T=chi(m+1)
   else:
    c=2*j
    T=sum((-1)**(m-r)*chi(r)/mp.mpf(c)**(m-r+1) for r in range(1,m+1))
    T+=(-1)**m/mp.mpf(c)**m*z**(-2*j)*(chi(1)-sum(z**(2*r+1)/(2*r+1) for r in range(j)))
   rhs+=d*T
  check('odd polylog sum b='+str(b)+' m='+str(m),lhs,rhs)

# One genuinely generalized-Stieltjes quadrature, at a separate precision.
with mp.workdps(35):
 lhs=mp.quad(lambda v:(1-v*v)**3*mp.stieltjes(1,2+v),[-1,0,1])
 rhs=mp.mpf(88)/3*mp.diff(mp.zeta,-3)+mp.mpf(137)/5*mp.diff(mp.zeta,-5)+8*mp.diff(mp.zeta,-3,2)+6*mp.diff(mp.zeta,-5,2)-mp.mpf(16)/15*mp.log(2)+mp.mpf(521)/900
 check('generalized Stieltjes gamma1 weighted integral',lhs,rhs,'1e-28')

result={'status':'PASS','checks':len(checks),'precision_digits':50,
        'stieltjes_precision_digits':35,'interval_certification':False,'results':checks}
(HERE/'numeric_results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
