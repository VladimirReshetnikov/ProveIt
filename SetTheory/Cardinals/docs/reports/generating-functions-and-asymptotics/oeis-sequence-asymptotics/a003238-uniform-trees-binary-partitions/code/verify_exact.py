"""Exact independent finite checks for uniform rooted trees and their sums."""
from pathlib import Path
from math import isqrt
import json,functools
ROOT=Path(__file__).resolve().parent

def recurrence(N):
 a=[0]*(N+1)
 if N:a[1]=1
 for n in range(1,N):
  total=0
  for d in range(1,isqrt(n)+1):
   if n%d==0:
    total+=a[d]
    if d*d!=n:total+=a[n//d]
  a[n+1]=total
 return a

def sieve(N):
 a=[0]*(N+1)
 if N:a[1]=1
 for d in range(1,N):
  for j in range(d+1,N+1,d):a[j]+=a[d]
 return a

@functools.lru_cache(None)
def divisible_partitions(n,last):
 if n==0:return 1
 return sum(divisible_partitions(n-k,k) for k in range(1,min(n,last)+1) if last%k==0)

def bfile(path):
 out={}
 for line in path.read_text().splitlines():
  if line.strip() and not line.startswith('#'):
   n,v=line.split()[:2];out[int(n)]=int(v)
 return out

if __name__=='__main__':
 a=recurrence(10000);b=sieve(10000)
 if a!=b:raise RuntimeError('two recurrence implementations disagree')
 for n in range(2,31):
  # First part is unrestricted; every later part divides its predecessor.
  got=sum(divisible_partitions(n-1-k,k) for k in range(1,n))
  if got!=a[n]:raise RuntimeError(('partition interpretation',n,got,a[n]))
 fix=bfile(ROOT/'b003238.txt');fixS=bfile(ROOT/'b003318.txt');checks=0
 for n,v in fix.items():
  if 1<=n<=10000:
   if a[n]!=v:raise RuntimeError(('OEIS',n));
   checks+=1
 s=0;checksS=0
 for n in range(1,10001):
  s+=a[n]
  if n in fixS:
   if s!=fixS[n]:raise RuntimeError(('partial sum OEIS',n))
   checksS+=1
 for n in range(2,10000):
  if a[n+1]<a[n]+1:raise RuntimeError('strict increase')
 print(json.dumps({'status':'PASS','recurrence_prefix':10000,'divisibility_partition_cases':29,'OEIS_A003238_cases':checks,'OEIS_A003318_cases':checksS,'strict_increase_cases':9998,'no_asserts':True},indent=2))
