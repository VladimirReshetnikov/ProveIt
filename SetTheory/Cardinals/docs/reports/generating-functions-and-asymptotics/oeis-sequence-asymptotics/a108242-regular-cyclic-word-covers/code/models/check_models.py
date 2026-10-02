"""Independent literal-necklace and logarithmic-product checks; portable paths."""
from itertools import product
from collections import Counter
from fractions import Fraction as F
from math import gcd
from pathlib import Path
import importlib.util,hashlib,json,re
ROOT=Path(__file__).resolve().parents[1]/'fixed'
spec=importlib.util.spec_from_file_location('cyclic',ROOT/'cyclic_covers.py');cyc=importlib.util.module_from_spec(spec);spec.loader.exec_module(cyc)
def phi(d):return sum(gcd(k,d)==1 for k in range(1,d+1))
def vecs(n,l):
 words={min(w[i:]+w[:i] for i in range(l)) for w in product(range(n),repeat=l)}
 return [tuple(w.count(i) for i in range(n)) for w in sorted(words)]
def direct(n,r,l,s):
 dp={(0,)*n:1}
 for deg in vecs(n,l):
  out=dp.copy()
  for v,c in dp.items():
   for k in range(1,n*r//l+1):
    v=tuple(a+b for a,b in zip(v,deg))
    if max(v)>r:break
    out[v]=out.get(v,0)+c
    if s==-1:break
  dp=out
 return dp.get((r,)*n,0)
def logarithm(n,r,l,s):
 log=Counter()
 for d in range(1,l+1):
  if l%d:continue
  for j in range(1,r//d+1):
   for slots in product(range(n),repeat=l//d):
    deg=tuple(slots.count(i)*j*d for i in range(n))
    if max(deg)<=r:log[deg]+=F(s**(j-1)*phi(d),l*j)
 dp={(0,)*n:F(1)}
 for deg,alpha in log.items():
  if not alpha:continue
  out=dp.copy()
  for v,c in dp.items():
   power=F(1)
   for k in range(1,n*r+1):
    v=tuple(a+b for a,b in zip(v,deg));power*=alpha/k
    if max(v)>r:break
    out[v]=out.get(v,F(0))+c*power
  dp=out
 return dp.get((r,)*n,F(0))
checked=[]
for n,r,l in product(range(1,5),range(1,5),range(3,6)):
 if n*r%l:continue
 for s in [1,-1]:
  a=direct(n,r,l,s);b=logarithm(n,r,l,s);assert a==b,(n,r,l,s,a,b)
  if r==l==3:assert a==cyc.exact(n,s)
  if r==2 and l==3:assert a==cyc.exact_degree2(n//3,s)
  checked.append(dict(n=n,r=r,ell=l,sign=s,count=a))
checks=json.loads((ROOT/'cyclic-checks.json').read_text())
for seq,s in [('A108242',1),('A110105',-1),('A110106',1),('A110104',-1)]:
 t=(ROOT/(seq+'.seq')).read_text();vals=[int(x) for x in ','.join(re.findall(r'^%[STU] '+seq+r' (.*)$',t,re.M)).split(',') if x]
 fn=cyc.exact if seq in ['A108242','A110105'] else cyc.exact_degree2
 assert all(fn(n,s)==v for n,v in enumerate(vals))
 assert checks[seq]['oeis_terms_checked']==len(vals)
 if fn==cyc.exact:assert list(map(str,cyc.coeffs(8,s)))==checks[seq]['relative_to_configuration']
hashes={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [ROOT/'cyclic_covers.py',ROOT/'cyclic-checks.json']}
out={'sources_sha256':hashes,'direct_necklace_comparisons':checked,'replayed_manifest':checks}
(Path(__file__).parent/'model-checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(checked),'independent direct-necklace/logarithm comparisons; 54 source OEIS terms; 8 coefficients per sign')
print(json.dumps(hashes,indent=2))
