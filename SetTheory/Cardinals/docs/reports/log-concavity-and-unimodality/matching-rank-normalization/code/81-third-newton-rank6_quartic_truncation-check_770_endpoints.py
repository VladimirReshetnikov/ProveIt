#!/usr/bin/env python3
from pathlib import Path
from math import lcm
import sympy as s,json,hashlib
ROOT=Path(__file__).resolve().parent
m,p,t,u,z,Z,y=s.symbols('m p t u z Z y')
D=12*m**3+7*m*m*p+12*m*m+2*m*p*p-12*m*p+6*m-6*p
A=18*m*m+6*m*p-36*m-18;B=72*m*m+6*m*p+36*m;C=12*m*m-29*m*p+12*m-p*p-12*p
L=(18*m*m+12*m*p-90*m-36)*t+72*m*m+24*m*p+30*m+6*p
Q=18*m**3+12*m*m*p+18*m*m+36*m*p+9*m+9*p
F=A*t*t+B*t+C+L*u-Q*u*u/p
# Compare the scalar with the independently derived symmetry reduction.
h,q=s.symbols('h q');source=ROOT.parent/'rank6_quartic_BB_audit'/'schur_770.txt'
old=s.sympify(source.read_text(),locals={str(x):x for x in [m,p,h,q,z]})
if s.cancel(old.subs({h:z*t,q:z*u})-z*z*F/D)!=0:raise RuntimeError('Schur scalar normalization mismatch')
# Fresh contraction of the independently generated class kernel.
a,b,c=s.symbols('a b c');data=json.loads((ROOT/'BB_M_centered_7_7.json').read_text());piv=data['pivots']
def cnt(cols):
 states={0}
 for col in cols:states={mask|(1<<i) for mask in states for i in range(3) if col>>i&1 and not mask>>i&1}
 return len(states)
x=q+3*h+3*z;vec=[x]+[q*(i+1).bit_count()+h*cnt([7,i+1])+z-x*(i+1).bit_count() for i in piv]
expr=0
for i,j,terms in data['entries']:
 cc=sum(s.Rational(v)*a**e[0]*b**e[1]*c**e[2]*p**e[3] for e,v in terms)
 expr+=cc*vec[i]*vec[j]*(1 if i==j else 2)
den=s.sympify(data['denominator'],locals=dict(a=a,b=b,c=c,p=p))
if s.cancel((expr/den).subs(a,m-b-c)-old)!=0:raise RuntimeError('Fresh class-kernel reconstruction mismatch')
upper=m*(m-1)/2;F0=F.subs(u,0);G=s.cancel(m*m*F.subs(u,p*t/m))
if s.degree(F0,p)!=2 or s.expand(F0).coeff(p,2)!=-1 or s.degree(G,p)!=2:raise RuntimeError('Concavity/Bernstein degree mismatch')
B0=G.subs(p,1);B1=B0+(upper-1)*s.diff(G,p).subs(p,1)/2;B2=G.subs(p,upper)
v=s.symbols('v')
if s.cancel(G.subs(p,1+v*(upper-1))-(B0*(1-v)**2+2*B1*v*(1-v)+B2*v*v))!=0:raise RuntimeError('Bernstein identity mismatch')
forms=[('F0_at_1',F0.subs(p,1)),('F0_at_upper',F0.subs(p,upper)),('G_B0',B0),('G_B1',B1),('G_B2',B2)]
records=[]
for label,f in forms:
 f=s.cancel(f.subs(t,m-(z+1)/2))
 for chart,sub in [('z_equals_1',{m:y+2,z:1}),('z_at_least_2',{m:Z+y+2,z:Z+2})]:
  poly=s.Poly(s.cancel(f.subs(sub)),Z,y);scale=lcm(*(int(s.denom(v)) for v in poly.coeffs()))
  terms=sorted((tuple(e),int(co*scale)) for e,co in poly.terms())
  if any(co<=0 for e,co in terms) or poly.coeff_monomial(1)<=0:raise RuntimeError(('Nonpositive coefficient or constant',label,chart))
  payload=json.dumps([[list(e),co] for e,co in terms],separators=(',',':'))
  records.append(dict(form=label,chart=chart,scale=scale,terms=[[list(e),co] for e,co in terms],count=len(terms),minimum=min(co for e,co in terms),constant=str(poly.coeff_monomial(1)),sha256=hashlib.sha256(payload.encode()).hexdigest()))
out={'scope':'Exact ten positive endpoint polynomials for BB core (7,7,0)','polynomials':len(records),'coefficient_entries':sum(r['count'] for r in records),'records':records}
(ROOT/'profile_770_endpoints.json').write_text(json.dumps(out,indent=2)+'\n');print(out['polynomials'],out['coefficient_entries'],'all coefficients and constants positive')
for r in records:print(r['form'],r['chart'],r['count'],r['constant'])
