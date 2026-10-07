"""Independent formal-exponential polynomial check of saddle corrections.
The implementation below uses a graded exponential differential recurrence;
it does not enumerate cumulant multiplicity vectors as saddle_engine does.
"""
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json,sys
from saddle_engine import correction

def addto(p,q,scale=F(1)):
 for d,v in q.items():p[d]=p.get(d,F(0))+scale*v

def mul(p,q):
 out={}
 for d,v in p.items():
  for e,w in q.items():out[d+e]=out.get(d+e,F(0))+v*w
 return out

def reference(r,P,b):
 G=2*r
 E=[{}]+[{g+2:b[g+2]/factorial(g+2)} for g in range(1,G+1)]
 Y=[{0:F(1)}]
 for g in range(1,G+1):
  out={}
  for d in range(1,g+1):addto(out,mul(E[d],Y[g-d]),F(d,g))
  Y.append(out)
 W={}
 for ell in range(G+1):addto(W,mul({ell:(-1)**ell*P[ell]/factorial(ell)},Y[G-ell]))
 out=F(0)
 for d,value in W.items():
  if d%2:continue
  moment=1
  for k in range(1,d,2):moment*=k
  out+=(-1)**(d//2)*moment*value/b[2]**(d//2)
 return out

rows=[]
for seed in range(1,17):
 P=[F((-1)**j*(seed+j*j+1),2*j+3) for j in range(9)]
 b=[F(0),F(1)]+[F(seed*seed+j,2*j-3) for j in range(2,11)]
 vals=[]
 for r in range(5):
  got=correction(r,P,b);expected=reference(r,P,b)
  if got!=expected:raise RuntimeError(('formal exponential mismatch',seed,r,got,expected))
  vals.append(str(got))
 rows.append({'seed':seed,'C0_through_C4':vals})
res={'status':'PASS','independent_method':'graded exponential differential recurrence and exact Gaussian moments','cases':len(rows)*5,'max_order':4,'rows':rows,'scope':'Exact algebraic coefficient engine check; not a proof of analytic asymptotic remainder.'}
print(json.dumps(res,indent=2))
