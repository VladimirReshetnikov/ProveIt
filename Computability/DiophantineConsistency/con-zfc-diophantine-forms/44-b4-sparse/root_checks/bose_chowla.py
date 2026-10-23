"""Independent explicit B_4 construction over GF(2^20); no external packages."""
import json,itertools,time
from pathlib import Path
D=20; M=(1<<D)-1; POLY=(1<<20)|(1<<3)|1

def xtime(a):
 a <<=1
 return a ^ POLY if a>>D else a

def mul(a,b):
 r=0
 while b:
  if b&1:r^=a
  b>>=1;a=xtime(a)
 return r

def power(a,k):
 r=1
 while k:
  if k&1:r=mul(r,a)
  a=mul(a,a);k>>=1
 return r

def make():
 # A full orbit of all nonzero bit vectors establishes a field and primitive x.
 logs=[-1]*(M+1);a=1
 for i in range(M):
  assert a and logs[a]<0,(i,a)
  logs[a]=i;a=xtime(a)
 assert a==1 and all(v>=0 for v in logs[1:])
 eta=power(2,M//31);sub=[0]+[power(eta,i) for i in range(31)]
 assert len(set(sub))==32 and all(power(a,32)==a for a in sub)
 assert all(a^b in sub and mul(a,b) in sub for a in sub for b in sub)
 raw=sorted(logs[2^a] for a in sub)
 # Translate after largest cyclic gap, minimizing maximum representative.
 best=min((max((a-b)%M for a in raw),b) for b in raw)
 shift=best[1];weights=sorted((a-shift)%M for a in raw)
 assert weights[0]==0 and len(set(weights))==32
 seen={}
 for tup in itertools.combinations_with_replacement(range(32),4):
  s=sum(weights[i] for i in tup)%M
  assert s not in seen,(tup,seen.get(s))
  seen[s]=tup
 out={'field_degree':20,'modulus_polynomial_bits':POLY,'group_order':M,'shift':shift,'weights_with_zero':weights,'witness_weights':weights[1:],'t':4*max(weights)+1,'four_multisets_checked':len(seen),'field_orbit_checked':M,'max_weight':max(weights),'source':'Bose-Chowla construction, independently generated'}
 return out
if __name__=='__main__':
 out=make();p=Path(__file__).with_name('bose_chowla_31.json');p.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
