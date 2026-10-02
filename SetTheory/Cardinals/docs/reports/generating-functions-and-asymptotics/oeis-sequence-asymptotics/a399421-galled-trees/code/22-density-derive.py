"""Portable replay adapter; the original arithmetic is unchanged.
All inputs and output destinations are explicit command-line options.
"""
import argparse, json, math
from pathlib import Path
import mpmath as mp
import sympy as sp
parser=argparse.ArgumentParser(description="Compute critical, Puiseux, and transfer constants.")
parser.add_argument('--rows', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('--row-limit', type=int, default=160)
parser.add_argument('--dps', type=int, default=80)
args=parser.parse_args()
mp.mp.dps=args.dps
rows=json.loads(args.rows.read_text())['rows']
if not 1 <= args.row_limit < len(rows): parser.error('row limit is outside supplied rows')
rows=rows[:args.row_limit+1]

def apoly(row,u):
 v=mp.mpf(0)
 for a in reversed(row):v=v*u+a
 return v

def G(z,u):
 v=mp.mpf(0)
 for row in reversed(rows):v=v*z+apoly(row,u)
 return v

def Phi(z,u,y):
 b=G(z*z,u*u)
 return z+(y*y+b)/2+u*z/2*((y/(1-y))**2+b/(1-b))

def crit(u):
 def eq(y):
  r=(1-y)**4/(u*y)
  return Phi(r,u,y)-y
 y=mp.findroot(eq,(mp.mpf('.42'),mp.mpf('.45')))
 r=(1-y)**4/(u*y)
 return r,y

r,tau=crit(mp.mpf(1));u=mp.mpf(1)
fz=mp.diff(lambda z:Phi(z,u,tau),r)
fu=mp.diff(lambda w:Phi(r,w,tau),u)
fyy=mp.diff(lambda y:Phi(r,u,y),tau,2)
fyz=mp.diff(lambda z:mp.diff(lambda y:Phi(z,u,y),tau),r)
fyu=mp.diff(lambda w:mp.diff(lambda y:Phi(r,w,y),tau),u)
mu=u*fu/(r*fz)
eta=(r*mu*fyz-u*fyu)/(tau*fyy)
fzz=mp.diff(lambda z:Phi(z,u,tau),r,2)
fzu=mp.diff(lambda z:mp.diff(lambda w:Phi(z,w,tau),u),r)
fuu=mp.diff(lambda w:Phi(r,w,tau),u,2)
q=[-r*mu,u,tau*eta]
v=(q[0]**2*fzz+2*q[0]*q[1]*fzu+2*q[0]*q[2]*fyz+q[1]**2*fuu+2*q[1]*q[2]*fyu+q[2]**2*fyy+mu**2*r*fz+u*fu)/(r*fz)
vals={'rho':r,'tau':tau,'B':G(r*r,u*u),'Phi_z':fz,'Phi_yy':fyy,'gamma':mp.sqrt(2*r*fz/fyy),'mu':mu,'variance':v,'eta':eta}
for k,x in vals.items():print(k,mp.nstr(x,65),flush=True)

N=14
Z=lambda:[mp.mpf(0)]*(N+1)
def add(*ps):return [sum(p[i] for p in ps) for i in range(N+1)]
def scale(p,a):return [a*x for x in p]
def mul(a,b):return [sum(a[j]*b[i-j] for j in range(i+1)) for i in range(N+1)]
def inv(a):
 b=Z();b[0]=1/a[0]
 for i in range(1,N+1):b[i]=-sum(a[j]*b[i-j] for j in range(1,i+1))/a[0]
 return b
one=Z();one[0]=1
z=Z();z[0]=r;z[2]=-r
b=Z()
for j in range(N//2+1):b[2*j]=(-1)**j*sum(mp.mpf(sum(row))*r**(2*n)*math.comb(2*n,j) for n,row in enumerate(rows) if 2*n>=j)
def H(y):
 yy=mul(y,y)
 frac=mul(y,inv(add(one,scale(y,-1))))
 gall=add(mul(frac,frac),mul(b,inv(add(one,scale(b,-1)))))
 return add(z,scale(add(yy,b),mp.mpf('.5')),scale(mul(z,gall),mp.mpf('.5')),scale(y,-1))
y=Z();y[0]=tau;y[1]=-vals['gamma']
for j in range(2,N):y[j]=-H(y)[j+1]/(fyy*y[1])
for j,c in enumerate(y[:N]):print('c'+str(j),mp.nstr(c,60),flush=True)

def transfer(alpha,m):
 aa=sp.Rational(alpha)
 L=[sp.Rational(0)]+[(-1)**(k+1)*(sp.bernoulli(k+1,-aa)-sp.bernoulli(k+1,1))/(k*(k+1)) for k in range(1,m+1)]
 g=[sp.Rational(1)]
 for k in range(1,m+1):g.append(sum(j*L[j]*g[k-j] for j in range(1,k+1))/k)
 return [mp.mpf(str(x.p))/int(x.q) for x in g]
C=y[1]/mp.gamma(-mp.mpf('.5'));cor=[mp.mpf(0)]*6
for ell in range(6):
 a=mp.mpf(ell)+mp.mpf('.5')
 for j,g in enumerate(transfer(sp.Rational(2*ell+1,2),5-ell)):
  cor[ell+j]+=y[2*ell+1]/mp.gamma(-a)*g/C
print('C',mp.nstr(C,65),flush=True)
for j,c in enumerate(cor):print('d'+str(j),mp.nstr(c,60),flush=True)
for n in [20,40,80,160]:
 if n>=len(rows):continue
 exact=mp.mpf(sum(rows[n]));lead=C*r**(-n)*mp.mpf(n)**(-mp.mpf('1.5'))
 print('check',n,'ratio',mp.nstr(exact/lead,30),'relative-errors',[mp.nstr((lead*sum(cor[j]/mp.mpf(n)**j for j in range(m+1))/exact)-1,12) for m in range(5)],flush=True)
args.output.parent.mkdir(parents=True,exist_ok=True)
args.output.write_text(json.dumps({**{k:mp.nstr(x,75) for k,x in vals.items()},'C':mp.nstr(C,75),'puiseux':[mp.nstr(x,75) for x in y[:N]],'corrections':[mp.nstr(x,75) for x in cor]},indent=2))
