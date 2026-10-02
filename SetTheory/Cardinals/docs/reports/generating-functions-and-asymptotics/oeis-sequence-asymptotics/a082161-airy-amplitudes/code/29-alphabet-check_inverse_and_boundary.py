#!/usr/bin/env python3
"""Independent algebraic boundary checks and numerical inverse-model tests."""
from decimal import Decimal as D, getcontext
from fractions import Fraction as Q
from pathlib import Path
import json
getcontext().prec=65
z=D('-2.338107410459767038489197252446735440638540145672387')
out={'scope':'Boundary equations exact; inverse numerical checks concern the explicit model, not effective sequence enclosures.','boundary':[],'inverse_model':[]}
for k in range(2,13):
 q=k-1
 assert q*q*Q(q,k)+q*(Q(q,k)+1)==k*k*Q(q,k)
 assert (q*q+1)+2*q==k*k
 assert Q(1,k)+q*(Q(1,k)+1)==k*k*Q(1,k)
 for r in range(q):
  assert Q(r)-k*Q(q,k)==r-q
  assert Q(r+1)-k==r-q
 assert Q(q)-k==-1 and -k*Q(1,k)==-1
 out['boundary'].append({'k':k,'physical_offsets':list(range(q,0,-1))+[1],'all_equations':'passed'})
for k in range(3,9):
 q=D(k-1);logC=D(2).ln()+D(k)*D(k).ln()-q*q.ln()
 loglambda=logC/q-1
 beta=3*z*(D(k)*q/2)**(D(1)/3)
 eta=D(7*k-5)/6
 def F(x):return q*x*(loglambda+x.ln())+beta*x**(D(1)/3)+eta*x.ln()
 errors=[]
 for exponent in [3,6,9,12,15]:
  n=D(10)**exponent;y=F(n);t=y/(q*y.ln())
  for _ in range(40):t-=(q*t*(loglambda+t.ln())-y)/(q*(1+loglambda+t.ln()))
  nu=t-(beta*t**(D(1)/3)+eta*t.ln())/(q*(1+loglambda+t.ln()))
  residual=abs(F(nu)-y)
  assert residual<D(1)
  assert abs(nu-n)*n.ln()<D(1)
  errors.append({'n':str(n),'residual':str(residual),'scaled_location_error':str(abs(nu-n)*n.ln())})
 assert all(D(errors[i+1]['residual'])<D(errors[i]['residual']) for i in range(len(errors)-1))
 out['inverse_model'].append({'k':k,'checks':errors})
Path(__file__).with_name('inverse-boundary-checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('Exact singular-boundary identities and high-precision inverse-model checks passed.')
