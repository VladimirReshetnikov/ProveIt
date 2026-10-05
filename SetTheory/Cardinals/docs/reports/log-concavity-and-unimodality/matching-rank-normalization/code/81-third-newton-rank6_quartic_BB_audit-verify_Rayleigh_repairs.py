"""Independent exact reconstruction of saved positive-Rayleigh decompositions.

The LP is not rerun or trusted. Rational multiplier lists are checked directly.
The underlying cleared Schur target remains linked to the primary raw output;
its separate rational-matrix reconstruction is an additional verification gate.
"""
from fractions import Fraction as F
from itertools import combinations_with_replacement,permutations
from collections import Counter
from math import comb,gcd
from functools import reduce
from pathlib import Path
import hashlib,json,sys
ROOT=Path(__file__).resolve().parent.parent/'rank6_quartic_truncation';OUT=Path(__file__).resolve().parent
Z=(0,)*7

def need(ok,msg):
 if not ok:raise RuntimeError(msg)
def add(a,b,scale=F(1)):
 d=dict(a)
 for e,c in b.items():d[e]=d.get(e,F(0))+scale*c
 return {e:c for e,c in d.items() if c}
def mul(a,b):
 d={}
 for e,c in a.items():
  for f,v in b.items():
   k=tuple(x+y for x,y in zip(e,f));d[k]=d.get(k,F(0))+c*v
 return {e:c for e,c in d.items() if c}
def variable(i):
 e=list(Z);e[i-1]=1;return {tuple(e):F(1)}
def choose(i,k):
 v={Z:F(1)}
 for j in range(k):v=mul(v,add(variable(i),{Z:F(-j)}))
 fact=1
 for j in range(1,k+1):fact*=j
 return {e:c/fact for e,c in v.items()}
def weight(types):
 v={Z:F(1)}
 for i,k in Counter(types).items():v=mul(v,choose(i,k))
 return v
def matching(rows,cols=3):
 return any(all(mask>>i&1 for mask,i in zip(rows,assignment)) for assignment in permutations(range(cols),len(rows)))
def translate(poly,basis):
 p=poly
 for i,b in sorted(Counter(x-1 for x in basis).items(),reverse=True):
  d={}
  for e,c in p.items():
   for j in range(e[i]+1):
    f=list(e);f[i]=j;f=tuple(f);d[f]=d.get(f,F(0))+c*comb(e[i],j)*b**(e[i]-j)
  p={e:c for e,c in d.items() if c}
 return p
TYPES=(1,2,3,5,6,7)
p={};h={};q={};m={}
for i in TYPES:m=add(m,variable(i))
for row in combinations_with_replacement(TYPES,2):
 if matching(tuple(x&3 for x in row),2):p=add(p,weight(row))
 if matching(row+(3,)):h=add(h,weight(row))
for row in combinations_with_replacement(TYPES,3):
 if matching(row):q=add(q,weight(row))
slack=add(mul(p,h),mul(m,q),F(-1));R={e:12*c for e,c in slack.items()}
need(all(c.denominator==1 for c in R.values()),'Rayleigh integrality')
need(reduce(gcd,(abs(int(c)) for c in R.values()))==1,'Rayleigh primitive scale')

def check(path):
 cert=json.loads(path.read_text());need(cert.get('success') and cert.get('exact'),'not an exact successful decomposition')
 core=cert['core'];basis=cert['basis'];data=json.loads((ROOT/('BB_certificate_%s_%s_%s_pairs.json'%tuple(core))).read_text())
 need(data['fixed_N4']==0 and F(data['rational_multiplier'])>0,'target normalization')
 rawpath=ROOT/('raw_%s_%s_%s_0.txt'%tuple(core));raw={}
 with rawpath.open() as f:
  length=int(f.readline())
  for line in f:
   key,c=map(int,line.split());e=tuple((key>>(6*i))&63 for i in range(7));need(e not in raw,'duplicate raw term');raw[e]=c
 need(len(raw)==length,'raw length');content=reduce(gcd,(abs(c) for c in raw.values()),0) or 1
 need(content==int(data['removed_content']),'primitive content')
 target=translate({e:F(c//content) for e,c in raw.items()},basis);ray=translate(R,basis);rem=target
 need(F(cert.get('rayleigh_scale',cert.get('rayleigh_denominator')))==12,'Rayleigh scale metadata')
 for e,w in cert['weights']:
  need(len(e)==7 and all(isinstance(v,int) and v>=0 for v in e),'invalid monomial')
  w=F(w);need(w>=0,'negative multiplier')
  term={tuple(a+b for a,b in zip(e,f)):w*c for f,c in ray.items()};rem=add(rem,term,F(-1))
 need(all(c>=0 for c in rem.values()),('negative exact remainder',path.name))
 for rec in data['records']:
  if rec['basis']==basis:
   text=json.dumps([[list(e),int(c)] for e,c in sorted(target.items())],separators=(',',':'))
   need(all(c.denominator==1 for c in target.values()),'noninteger target')
   need(hashlib.sha256(text.encode()).hexdigest()==rec['sha256'],'target hash linkage')
 digest=hashlib.sha256(json.dumps([[list(e),str(c)] for e,c in sorted(rem.items())],separators=(',',':')).encode()).hexdigest()
 out={'core':core,'basis':basis,'all_pass':True,'positive_multiplier_terms':len(cert['weights']),'remainder_terms':len(rem),'minimum_remainder':str(min(rem.values(),default=0)),'remainder_sha256':digest,'repair_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'raw_target_sha256':hashlib.sha256(rawpath.read_bytes()).hexdigest()}
 print('PASS',core,basis,len(cert['weights']),len(rem),flush=True);return out
if __name__=='__main__':
 paths=[Path(v) for v in sys.argv[1:]] if len(sys.argv)>1 else sorted(ROOT.glob('Rayleigh_cone_*_1_2.json'))
 results=[]
 for path in paths:
  d=json.loads(path.read_text())
  if d.get('success') and d.get('exact'):results.append(check(path))
 out={'all_saved_successes_pass':True,'certificates':len(results),'Rayleigh_scale':'12','records':results}
 (OUT/'Rayleigh_repair_checks.json').write_text(json.dumps(out,indent=2)+'\n');print('VERIFIED',len(results),'exact repair identities')
