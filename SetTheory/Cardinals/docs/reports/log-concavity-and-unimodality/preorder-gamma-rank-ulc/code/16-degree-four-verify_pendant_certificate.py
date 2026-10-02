"""Standalone exact-arithmetic verifier for the complete marked-core certificate.
No external algebra packages or enumeration executable required.
"""
from pathlib import Path
import csv,json
path=Path(__file__).with_name('pendant10_coefficients.csv')
def product(p,q):
 r=[0]*(len(p)+len(q)-1)
 for i,x in enumerate(p):
  for j,y in enumerate(q):r[i+j]+=x*y
 return r
count=negative_linear=0;min_disc=None
with path.open() as f:
 for row in csv.DictReader(f):
  a=[int(row[f'a{k}']) for k in range(5)]
  b=[int(row[f'b{k}']) for k in range(4)]
  assert a[0]==b[0]==1 and b[3]>0
  gamma=[[a[0],0]]+[[a[k],b[k-1]] for k in range(1,5)]
  for k,left,right in ((1,3,8),(2,4,9),(3,3,8)):
   square=product(gamma[k],gamma[k]);adjacent=product(gamma[k-1],gamma[k+1])
   C,B,A=[left*x-right*y for x,y in zip(square,adjacent)]
   assert A>=0 and C>=0,(row,k,[C,B,A])
   if B<0:
    negative_linear+=1;disc=4*A*C-B*B
    assert disc>=0,(row,k,[C,B,A],disc)
    min_disc=disc if min_disc is None else min(min_disc,disc)
  count+=1
print(json.dumps({'distinct_marked_core_gamma_pairs':count,'verified_quadratics':3*count,'negative_linear_coefficients':negative_linear,'minimum_4AC_minus_B2_when_B_negative':min_disc,'status':'PASS'},sort_keys=True))
