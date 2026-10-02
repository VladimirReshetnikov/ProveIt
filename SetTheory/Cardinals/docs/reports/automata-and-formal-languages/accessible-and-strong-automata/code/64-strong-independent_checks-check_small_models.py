"""Brute-force graph checks and finite-difference renewal checks.
No imports from the proposed generator.
"""
from itertools import product
from math import comb,factorial
import json
from pathlib import Path

def count_strong(k,n):
 total=0
 for f in product(range(n),repeat=k*n):
  out=[0]*n;rev=[0]*n
  for i,j in enumerate(f):
   source=i//k;out[source]|=1<<j;rev[j]|=1<<source
  success=True
  for edges in (out,rev):
   reached=1;front=1
   while front:
    pos=(front&-front).bit_length()-1;front&=front-1
    new=edges[pos]&~reached;reached|=new;front|=new
   if reached!=(1<<n)-1:success=False;break
  total+=success
 return total

def exact_P(k,N):
 A=[0]*(N+1)
 for n in range(1,N+1):A[n]=n**(k*n)-sum(comb(n,h)*n**(k*(n-h))*A[h] for h in range(1,n))
 return [A[n]//factorial(n) for n in range(N+1)]

def renewal_check(k,N):
 P=exact_P(k,N);stirling=[0]*(N+1);stirling[0]=1;T={}
 for m in range(1,k*N+1):
  stirling=[0]+[stirling[j-1]+j*stirling[j] for j in range(1,N+1)]
  if m%k==0:T[m//k]=stirling[m//k]
 for n in range(1,N+1):
  value=P[n]
  for h in range(1,n):
   r=n-h
   numerator=sum((-1)**(r-j)*comb(r,j)*(h+j)**(k*r) for j in range(r+1))
   assert numerator%factorial(r)==0
   value+=P[h]*numerator//factorial(r)
  assert value==T[n],(k,n,value,T[n])
 return True

results={'brute_force':[],'renewal_checks':[]}
for k,n in ((2,4),(3,3),(4,3)):
 count=count_strong(k,n);results['brute_force'].append({'k':k,'n':n,'count':count});print(k,n,count,flush=True)
for k in (2,3,4,5,6):
 results['renewal_checks'].append({'k':k,'through_n':25,'passed':renewal_check(k,25)})
p=Path(__file__).with_name('small_models.json');p.write_text(json.dumps(results,indent=2)+'\n')
