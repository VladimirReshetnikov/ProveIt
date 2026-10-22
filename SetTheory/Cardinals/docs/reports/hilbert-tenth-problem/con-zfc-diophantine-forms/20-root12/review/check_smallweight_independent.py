#!/usr/bin/env python3
from pathlib import Path
import json,random
from collections import Counter
from sympy.polys.rings import ring
from sympy.polys.domains import GF
ROOT=Path(__file__).resolve().parents[1]
NAMES=['Jrep','F','alpha','transport_quotient','s','eta','zeta']
rng=random.Random(271004)
def ev(p,values):
 v=dict(values)
 for n,op,a,b in p['source']:
  a=a if isinstance(a,int) else v[a];b=b if isinstance(b,int) else v[b]
  v[n]=a+b if op=='+' else a-b if op=='-' else a*b
 return v

def direct(v):
 J,F,alpha,z,h,i,T,s,w,eta,zeta,gamma,t=[v[n] for n in ['Jrep','F','alpha','transport_quotient','h','i','auxiliary_quotient','s','w','eta','zeta','gamma','t']]
 q=v['Bm1']*J+1;cw=q-F-alpha;X=w*q;Y=s*q**3;E=X*Y;k=eta+zeta;c=k*Y+eta;a=E+Y;H=4*a+3;delta=a*a+H
 R=((q-1)*(q-F)+alpha)*(q*q-1)+(v['MC']+q*v['MF'])*J
 Nmain=(X+a*c+gamma*H)**2-delta*c*c;Nk=k-h*E-R;Nt=(v['Kconstant']+w)*cw+q-F-z*(q-1)
 lf=E*k*Y;A=1+lf*(lf+k);I=i*c*c;D=1+delta*I*I;Q=(delta*I)**2;d=Q-1;vv=c*T;b=c+R*D
 ee=Q*(D*vv*vv+b*b)-1;B=2*Q*vv*b;M=I*I+T*T;C=d*(t*t+M*M*A)-ee;U=C*C+D*B*B-4*d*d*t*t*M*M*A
 return Nmain*Nk*Nt*(1+U*U-4*D*C*C*B*B)-1
out=[]
for name,n,ops,deg in [('polynomial13_84_smallweight',13,84,515),('integer27_product136_smallweight',27,136,1004)]:
 p=json.loads((ROOT/'arithmetic'/f'{name}.json').read_text())
 for _ in range(100):
  vals={x:rng.randrange(-3,4) for x in p['witnesses']+p['fixed_numerals']}
  canonical=dict(vals)
  if n==27:
   for v in NAMES:
    x,y,z=[vals[f'{v}_{r}'] for r in ['x','y','z']]
    canonical[v]=1+x*x+x+y*y+z*z
   canonical['i']=2*vals['odd_i_parameter']+1;canonical['w']=vals['square_w_parameter']**2
  assert direct(canonical)==ev(p,vals)[p['output']]
 assert len(set(p['witnesses']))==n and len(p['source'])==ops
 counts=Counter(r[1] for r in p['source'])
 R,x=ring('x',GF(1000000033))
 vals={v:rng.randrange(1,17)+rng.randrange(1,17)*x for v in p['witnesses']}
 vals.update({v:R(z) for v,z in zip(p['fixed_numerals'],[31,127,10,45])})
 degree=ev(p,vals)[p['output']].degree()
 assert degree==deg,(degree,deg)
 out.append({'packet':name,'variables':n,'operations':ops,'multiplications':counts['*'],'additions_subtractions':counts['+']+counts['-'],'independent_signed_cases':100,'independent_SymPy_GF_univariate_degree':degree,'prime':1000000033})
receipt={'status':'PASS','checks':out,'scope':'Separate direct formula and seven-Pos/odd-i/square-w substitution evaluation, plus independent SymPy finite-field polynomial-line audit. Uniform degree proof and semantic proof separately reviewed; no compiler or logical endpoint kernel check.'}
(ROOT/'review/SMALLWEIGHT_INDEPENDENT_CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
