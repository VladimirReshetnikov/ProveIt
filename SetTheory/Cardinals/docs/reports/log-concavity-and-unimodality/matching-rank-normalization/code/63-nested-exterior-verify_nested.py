"""Independent integer certificate for a complete 3x3 core and nested right neighborhoods.
Counts via nested Hall inequalities, not a matching recursion. No code is imported
from the certificate under review. Coefficients are in z=n-3 and scaled by 36.
"""
from itertools import product
from functools import lru_cache
from math import comb
from pathlib import Path
import json,hashlib
ROOT=Path(__file__).resolve().parents[1]/'data'
CH=((6,0,0,0),(18,6,0,0),(18,15,3,0),(6,11,6,1))

def chain_matches(counts,mask):
 return counts[0]<=bool(mask&1) and counts[0]+counts[1]<=(mask&3).bit_count() and sum(counts)<=mask.bit_count()

@lru_cache(None)
def T(j,counts,deleted=False):
 q=sum(counts)
 if q>3:return (0,)*4
 ret=[0]*4
 for mask in range(8):
  i=mask.bit_count();ell=j+q-i
  if not chain_matches(counts,mask) or not 0<=ell<=j:continue
  if deleted and i!=q:continue
  for d,c in enumerate(CH[ell]):ret[d]+=c
 return tuple(ret)

@lru_cache(None)
def mul(u,v):
 r=[0]*7
 for i,a in enumerate(u):
  for j,b in enumerate(v):r[i+j]+=a*b
 return tuple(r)

def coefficient(k,v,d,o):
 db=v.count(2);sb=v.count(1);ans=[0]*7
 for e in product(*(range(x+1)for x in o)):
  r1=tuple(x+y for x,y in zip(d,e));r2=tuple(x+y-z for x,y,z in zip(d,o,e))
  if sum(r1)>3 or sum(r2)>3:continue
  ways=1
  for n,j in zip(o,e):ways*=comb(n,j)
  for j in range(sb+1):
   b1=db+j;b2=db+sb-j;degree=b1+sum(r1)
   if degree==k:factor=k*(6-k)
   elif degree==k-1:factor=-(k+1)*(7-k)
   else:continue
   f=mul(T(b1,r1),T(b2,r2));q=mul(T(b1,r1,True),T(b2,r2,True))
   mult=factor*ways*comb(sb,j)
   for n in range(7):ans[n]+=mult*(f[n]-q[n])
 return ans

def triples(cap):return [v for v in product(range(cap+1),repeat=3)if sum(v)<=cap]

def generate():
 records=[];nonzero=0;counts={k:0 for k in range(2,6)};nz={k:0 for k in range(2,6)}
 for d in triples(3):
  for o in triples(6-2*sum(d)):
   for v in product(range(3),repeat=3):
    degree=sum(v)+sum(o)+2*sum(d)
    if degree%2 or not 4<=degree<=10:continue
    k=degree//2;c=coefficient(k,v,d,o)
    assert all(x>=0 for x in c),(k,v,d,o,c)
    counts[k]+=1
    if any(c):nonzero+=1;nz[k]+=1
    records.append(dict(k=k,core_exponents=v,repeated_exterior_counts=d,single_exterior_counts=o,gap_increment_coefficients_times_36=c))
 assert len(records)==3391
 out={'scope':'Complete 3x3 core; unit activities on A and n>=3 common exterior-left vertices; arbitrary positive right activities; exterior-right neighborhoods in the chain 1,3,7.','normalization':'36 times each gap increment, expanded in nonnegative z=n-3','patterns':len(records),'patterns_by_gap':counts,'nonzero':nonzero,'nonzero_by_gap':nz,'all_coefficients_nonnegative':True,'records':records}
 assert json.loads((ROOT/'exact_certificate.json').read_text())==json.loads(json.dumps(out)), 'Stored certificate differs from exact reconstruction'
 summary={k:v for k,v in out.items()if k!='records'}
 (ROOT/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
 print(json.dumps(summary,indent=2))
 return out

if __name__=='__main__':generate()
