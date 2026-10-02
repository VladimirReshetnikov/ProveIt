"""Portable replay adapter; the original arithmetic is unchanged.
All inputs and output destinations are explicit command-line options.
"""
import argparse, json, math
from pathlib import Path
import mpmath as mp
parser=argparse.ArgumentParser(description="Compute proportional-density saddle checks.")
parser.add_argument('--rows', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('--dps', type=int, default=55)
args=parser.parse_args()
mp.mp.dps=args.dps
rows=json.loads(args.rows.read_text())['rows']
if len(rows)<=160: parser.error('rows through n=160 are required')
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

def crit(s):
 u=mp.exp(s)
 def eq(y):
  r=(1-y)**4/(u*y)
  return Phi(r,u,y)-y
 guess=1/(1+(1/mp.mpf('.435')-1)*u**mp.mpf('.348'))
 y=mp.findroot(eq,(guess*mp.mpf('.99'),guess*mp.mpf('1.01')))
 r=(1-y)**4/(u*y)
 return r,y

def f(s):return -mp.log(crit(s)[0])
def C(s):
 u=mp.exp(s);r,y=crit(s)
 fz=mp.diff(lambda z:Phi(z,u,y),r)
 fyy=1+u*r*(1+2*y)/(1-y)**4
 return mp.sqrt(2*r*fz/fyy)/(2*mp.sqrt(mp.pi))

def d1(s):
 u=mp.exp(s);r,y=crit(s)
 fz=mp.diff(lambda z:Phi(z,u,y),r);fzz=mp.diff(lambda z:Phi(z,u,y),r,2)
 fyy=1+u*r*(1+2*y)/(1-y)**4
 fyz=u*y/(1-y)**3;fyyz=u*(1+2*y)/(1-y)**4
 fyyy=6*u*r*(1+y)/(1-y)**5;fyyyy=12*u*r*(3+2*y)/(1-y)**6
 c1=-mp.sqrt(2*r*fz/fyy)
 c2=r*fyz/fyy-fyyy*c1*c1/(6*fyy)
 c3=(-fyy*c2*c2/2+r*fyz*c2-r*r*fzz/2+r*fyyz*c1*c1/2-fyyy*c1*c1*c2/2-fyyyy*c1**4/24)/(fyy*c1)
 return mp.mpf(3)/8-mp.mpf(3)*c3/(2*c1)

mu=mp.diff(f,mp.mpf(0));beta=mp.diff(f,mp.mpf(0),2)
print('C log derivative at 0',mp.nstr(mp.diff(lambda s:mp.log(C(s)),mp.mpf(0)),35),flush=True)
print('C log second derivative at 0',mp.nstr(mp.diff(lambda s:mp.log(C(s)),mp.mpf(0),2),35),flush=True)
results=[]
for a in [mp.mpf('.1'),mp.mpf('.2'),mp.mpf('.3')]:
 s=mp.findroot(lambda t:mp.diff(f,t)-a,(a-mu)/beta)
 u=mp.exp(s);r,y=crit(s);be=mp.diff(f,s,2);c=C(s);f3=mp.diff(f,s,3);f4=mp.diff(f,s,4)
 cp=mp.diff(C,s);cpp=mp.diff(C,s,2)
 e1=d1(s)-cpp/(2*c*be)+cp*f3/(2*c*be**2)+f4/(8*be**2)-5*f3*f3/(24*be**3)
 print('density',mp.nstr(a),'u',mp.nstr(u,35),'rho',mp.nstr(r,35),'beta',mp.nstr(be,35),'e1',mp.nstr(e1,35),flush=True)
 entry={'alpha':str(a),'u':mp.nstr(u,45),'rho':mp.nstr(r,45),'beta':mp.nstr(be,45),'e1':mp.nstr(e1,45),'checks':[]}
 for n in [20,40,80,160]:
  k=int(a*n);assert mp.mpf(k)/n==a
  exact=mp.mpf(rows[n][k]);lead=c*r**(-n)*u**(-k)/(mp.sqrt(2*mp.pi*be)*n*n)
  err0=lead/exact-1;err1=lead*(1+e1/n)/exact-1
  print('check',n,k,'lead-error',mp.nstr(err0,18),'one-correction-error',mp.nstr(err1,18),'n2err',mp.nstr(n*n*err1,14),flush=True)
  entry['checks'].append({'n':n,'k':k,'leading_relative_error':mp.nstr(err0,30),'corrected_relative_error':mp.nstr(err1,30)})
 results.append(entry)
args.output.parent.mkdir(parents=True,exist_ok=True)
args.output.write_text(json.dumps(results,indent=2))
