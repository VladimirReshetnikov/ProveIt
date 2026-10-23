"""Exact independent fixtures for signed-to-positive Pell orbit restoration."""
from pathlib import Path
import json

def mul(a,b,D):return (a[0]*b[0]+D*a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def mpow(a,n,D,mod=None):
 out=(1,0)
 while n:
  if n&1:out=mul(out,a,D);out=tuple(v%mod for v in out) if mod else out
  a=mul(a,a,D);a=tuple(v%mod for v in a) if mod else a;n//=2
 return out
count=0;negative=zero=0
for G in range(2,12):
 D=G*G-1
 for C in range(1,8):
  for F in range(1,8):
   M=C*F
   for order in range(1,10001):
    if mpow((G,1),order,D,M)==(1%M,0):break
   else:raise AssertionError('order not found')
   unit=mpow((G,1),order,D)
   for index in [-3,-1,0,1,3]:
    x,H=mpow((G,1),abs(index),D)
    if index<0:H=-H
    old=(x,H);new=old;threshold=10*C*F+abs(H)
    for steps in range(1,30):
     new=mul(new,unit,D)
     if new[1]>threshold:break
    else:raise AssertionError('positive orbit did not grow')
    assert new[0]**2-D*new[1]**2==1
    assert (new[1]-H)%M==0 and (new[0]-x)%M==0
    count+=1;negative+=index<0;zero+=index==0
out={'status':'PASS','exact_orbit_fixtures':count,'negative_initial_H':negative,'zero_initial_H':zero,'scope':'Finite exact fixtures supplement the universal finite-group Pell-orbit proof.'}
Path(__file__).with_name('PELL_ORBIT_CHECKS.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
