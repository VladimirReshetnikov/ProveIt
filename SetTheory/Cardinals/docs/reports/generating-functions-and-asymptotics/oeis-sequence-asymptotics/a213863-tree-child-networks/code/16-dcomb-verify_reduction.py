#!/usr/bin/env python3
"""Exact finite replay: source b array versus shifted A array and gauge cocycle."""
from math import comb, factorial
from fractions import Fraction as F
from pathlib import Path
import json
rows=[]
for d in range(2,9):
 L=F((d+1)**(d-1),factorial(d-1)); As=[[1]]; bs={1:[0,1]}; cs=[1,1]
 for n in range(1,15):
  prev=As[-1]; cur=[comb(d*n-1,d-1)*prev[0]]
  for k in range(1,n+1):cur.append(cur[-1]+comb(d*n+k-1,d-1)*(prev[k] if k<n else 0))
  As.append(cur)
 for n in range(2,15):
  prev=bs[n-1]; cur=[0]
  for m in range(1,n+1):cur.append(comb(d*n+m-2,d-1)*sum(prev[1:m+1]))
  bs[n]=cur;cs.append(sum(cur))
 for n in range(1,15):
  assert As[n][n]==cs[n]
  for k in range(n):assert As[n][k]==sum(bs[n][1:k+2])
 D={}
 for N in range(29):
  for j in range(N%2,N+1,2):
   n,k=(N+j)//2,(N-j)//2
   if n<15:D[N,j]=F(As[n][k],L**n*factorial(n)**(d-1))
 def p(N,j):
  out=F(1)
  for h in range(1,d):out*=1-F(2*(j+h),(d+1)*(N+j))
  return out
 checks=0
 for (N,j),v in D.items():
  if N==0:continue
  if (N-1,j+1) not in D and j!=N:continue
  assert v==D.get((N-1,j+1),0)+(p(N,j)*D.get((N-1,j-1),0) if j else 0)
  checks+=1
 # Squared gauge identities avoid introducing radicals.
 for N in range(2,20):
  gn=gm=F(1)
  for j in range(1,N+2):
   assert F(1,(d+1)**(d-1))<=p(N,j)<=1
   assert p(N-1,j)<p(N,j)
   gn*=p(N,j);gm*=p(N-1,j)
   assert 0<gm/gn<=1
 rows.append({'d':d,'diagonal':cs[:9],'exact_recurrence_checks':checks,'gauge_contractivity_checks':True})
Path(__file__).with_name('reduction-checks.json').write_text(json.dumps(rows,indent=2)+'\n')
print('PASS: d=2,...,8, source-array identities, shifted recurrence, normalized recurrence, positive monotone gauge')
