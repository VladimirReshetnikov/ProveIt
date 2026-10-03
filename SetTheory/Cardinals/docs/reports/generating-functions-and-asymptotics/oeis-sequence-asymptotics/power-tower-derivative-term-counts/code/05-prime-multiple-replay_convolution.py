#!/usr/bin/env python3
from fractions import Fraction as Q
from math import factorial,gcd,lcm
from pathlib import Path
import json
R=60; YMAX=120
h=[Q(1)]+[Q((-1)**(j-1),j*(j+1)) for j in range(1,R+1)]
f=[Q(1)]+[Q(0)]*R;table=[f]
for y in range(1,YMAX+1):
 f=[sum((f[i]*h[n-i] for i in range(n+1)),Q(0)) for n in range(R+1)]
 table.append(f)
primes=[2,3,5,7,11,13,17,19,23,29,31]
nonzero=local=lift=0
for p in primes:
 if 2*(p-1)<=R:
  for y in range(1,YMAX+1):
   assert table[y][2*(p-1)]!=0;nonzero+=1
 for m in range(2,p):
  r=m*(p-1)
  if r>R:break
  for y in range(1,YMAX+1):
   if table[y][r]==0:assert any((y-j)%p**(m-j+1)==0 for j in range(1,m))
   local+=1
  for j in range(1,m):
   v=table[j][r]*p**m
   assert v.denominator%p
   assert v.numerator%p**(m-j+1)==0;lift+=1
# Reconstruct the degree-eight polynomial solely from nine direct integer powers.
values=[table[y][8] for y in range(9)];fall=[Q(1)];coeff=[Q(0)]*9
for j in range(9):
 c=values[0]/factorial(j)
 for k,v in enumerate(fall):coeff[k]+=c*v
 values=[values[i+1]-values[i] for i in range(len(values)-1)]
 new=[Q(0)]*(len(fall)+1)
 for k,v in enumerate(fall):new[k]-=j*v;new[k+1]+=v
 fall=new
D=lcm(*(x.denominator for x in coeff));ints=[int(x*D) for x in coeff];g=gcd(*ints);primitive=[x//g for x in ints[1:]]
expected=[-122821584,172998164,-89214420,22538215,-3075240,229950,-8820,135]
assert primitive==expected
res=[sum(c*y**i for i,c in enumerate(primitive))%11 for y in range(11)]
assert all(res)
# Exact derivative bridge via independently multiplied consecutive-root polynomial.
bridge=0
for M in range(2,50):
 P=[1]
 for z in range(M):
  PP=[0]*(len(P)+1)
  for k,c in enumerate(P):PP[k]-=z*c;PP[k+1]+=c
  P=PP
 for y in range(1,M):
  val=sum(Q(P[k]*factorial(k),factorial(k-y))*y**(k-y) for k in range(y,M+1))/factorial(M)
  assert val==table[y][M-y];bridge+=1
out=dict(algorithm='direct rational power convolution and finite-difference interpolation, independent of polynomial logarithm recurrence',max_offset=R,max_exponent=YMAX,complete_double_family_checks=nonzero,localization_checks=local,small_exponent_lift_checks=lift,derivative_bridge_checks=bridge,primitive_r8=primitive,mod11_values=res,all_pass=True)
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
