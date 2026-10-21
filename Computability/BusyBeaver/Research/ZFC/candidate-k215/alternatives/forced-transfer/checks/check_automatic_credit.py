from functools import lru_cache
from math import isqrt
import json
from pathlib import Path
import argparse
ap=argparse.ArgumentParser();ap.add_argument("--out",type=Path,required=True);args=ap.parse_args();args.out.mkdir(parents=True,exist_ok=True)
if not __debug__:raise SystemExit("Assertions required")

def unpair(n):
 q=(isqrt(8*n+1)-1)//2
 y=n-q*(q+1)//2
 return q-y,y
@lru_cache(None)
def words(n):
 a,y=unpair(n)
 if a==0: r=y; w=-1; label='S'
 elif a==1: r=unpair(y)[1]; w=-1; label='M'
 else: r=unpair(unpair(y)[1])[1]; w=10; label='AX'
 return [(label,w)] + (words(r-1) if r else [])
bal=0;minimum=0;records=[]
for n in range(1,64):
 start=bal;local=0;low=0
 for label,w in words(n):
  bal+=w;minimum=min(minimum,bal);local+=w;low=min(low,local)
 records.append(dict(n=n,word=words(n),start=start,end=bal,local_minimum=low,cumulative_minimum=minimum))
print('minimum',minimum,'first',[r for r in records if r['n']<7])
counts=[sum(1 for a,w in words(n)if w<0)for n in range(10000)]
s=0
for n,k in enumerate(counts):
 s+=k;assert s<=2*(n+1),(n,s)
(args.out/'AUTOMATIC_CREDIT.json').write_text(json.dumps(dict(status='FINITE_CHECK_PASS',minimum=minimum,records=records,count_check_limit=len(counts)),indent=2))
