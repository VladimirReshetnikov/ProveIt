from pathlib import Path
from itertools import combinations_with_replacement,product
from collections import Counter
from math import comb,gcd,lcm
from functools import reduce
import json,hashlib,subprocess,sys,time
import sympy as s
from endpoint_core import endpoint,N
HERE=Path(__file__).resolve().parent;SNAP=HERE.parent/'audit_snapshot'
EXPECTED=json.loads((SNAP/'stable_expected.json').read_text())
BASES=[x for x in combinations_with_replacement((1,2,3,5,6,7),2) if (x[0]&1 and x[1]&2) or (x[0]&2 and x[1]&1)]
if len(BASES)!=15:raise RuntimeError('bases')
def digest(poly):
 return hashlib.sha256(json.dumps([[list(e),v] for e,v in sorted(poly.items())],separators=(',',':')).encode()).hexdigest()
def shifted(poly,basis):
 shifts=Counter(i-1 for i in basis);out={}
 for e,v in poly.items():
  for ks in product(*(range(e[i]+1) for i in shifts)):
   f=list(e);w=v
   for (i,b),k in zip(shifts.items(),ks):f[i]=k;w*=comb(e[i],k)*b**(e[i]-k)
   f=tuple(f);out[f]=out.get(f,0)+w
 return {e:v for e,v in out.items() if v}
def one(rec):
 start=time.time();core=tuple(rec['core_columns']);tag='_'.join(map(str,core));cache=json.loads((SNAP/f'BB_M_centered_{core[0]}_{core[1]}.json').read_text())
 raw=[endpoint(core,0)]+[endpoint(core,i+1) for i in cache['pivots']]
 vec=[raw[0]]+[v-raw[0]*(i+1).bit_count() for i,v in zip(cache['pivots'],raw[1:])]
 cv=lcm(*(int(s.denom(c)) for v in vec for c in v.coeffs()))
 entries=cache['entries'];cm=lcm(*(int(s.denom(s.Rational(c))) for i,j,terms in entries for e,c in terms));maxp=max(e[3] for i,j,terms in entries for e,c in terms)
 bound=max(sum(e[:3])+2*e[3]+6 for i,j,terms in entries for e,c in terms)
 if bound>=32:raise RuntimeError(('packing bound',core,bound))
 inp=HERE/f'input_{tag}.txt';outp=HERE/f'product_{tag}.txt'
 with inp.open('w') as f:
  f.write(str(len(vec))+'\n')
  for v in vec:
   f.write(str(len(v.terms()))+'\n')
   for e,c in v.terms():f.write(' '.join(map(str,e))+' '+str(int(c*cv))+'\n')
  f.write(str(len(entries))+'\n')
  for i,j,terms in entries:
   f.write(f'{i} {j} {len(terms)}\n')
   for e,c in terms:f.write(' '.join(map(str,e))+' '+str(int(s.Rational(c)*cm)*2**(maxp-e[3]))+'\n')
 with inp.open() as fi,outp.open('w') as fo:subprocess.run([str(HERE/'independent_product')],stdin=fi,stdout=fo,check=True)
 poly={}
 with outp.open() as f:
  size=int(f.readline())
  for line in f:
   x=list(map(int,line.split()));poly[tuple(x[:7])]=x[7]
 if len(poly)!=size:raise RuntimeError('product length')
 content=reduce(gcd,(abs(v) for v in poly.values()),0) or 1
 poly={e:v//content for e,v in poly.items() if v}
 multiplier=s.Rational(cv*cv*cm*2**maxp,content)
 if str(multiplier)!=rec['rational_multiplier']:raise RuntimeError(('multiplier',core,str(multiplier),rec['rational_multiplier']))
 if len(poly)!=rec['base_terms']:raise RuntimeError(('base terms',core))
 repaired=list(core) in EXPECTED['rayleigh_cores'];records=[]
 refs={tuple(r['basis']):r for r in rec['records']}
 for basis in BASES:
  p=shifted(poly,basis);sha=digest(p);minimum=min(p.values(),default=0);neg=sum(v<0 for v in p.values())
  if not repaired and neg:raise RuntimeError(('negative',core,basis))
  if basis in refs:
   r=refs[basis]
   if (len(p),minimum,sha)!=(r['terms'],r['minimum'],r['sha256']):raise RuntimeError(('hash mismatch',core,basis))
  records.append(dict(basis=basis,terms=len(p),minimum=minimum,negative=neg,sha256=sha))
 result=dict(core=core,passed=True,repaired=repaired,records=records,multiplier=str(multiplier),base_terms=len(poly),base_sha256=digest(poly),seconds=time.time()-start)
 (HERE/f'replay_{tag}.json').write_text(json.dumps(result,indent=2)+'\n');print(tag,'PASS',len(poly),'terms',round(time.time()-start,2),'sec',flush=True)
if __name__=='__main__':
 shard=int(sys.argv[1]) if len(sys.argv)>1 else 0;parts=int(sys.argv[2]) if len(sys.argv)>2 else 1
 for i,rec in enumerate(EXPECTED['profiles']):
  if i%parts==shard:one(rec)
