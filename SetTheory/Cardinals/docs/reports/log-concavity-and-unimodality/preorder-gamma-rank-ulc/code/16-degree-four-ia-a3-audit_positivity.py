#!/usr/bin/env python3
"""Fresh exact a3 positivity audit; standard library only, no producer imports.
Rebuilds 6*gamma, both gaps, finite-difference Newton coefficients, every required
0/(1+y) population face, each alias and all monomial-weighted rational squares.
"""
from pathlib import Path
from fractions import Fraction
from collections import Counter
from itertools import product, zip_longest
from math import comb, factorial, gcd
from functools import lru_cache
import json, hashlib, time
D=Path('/workspace/shared/preorder-gamma-degree4/three-attachment')
O=Path(__file__).parent
START=time.time(); C=Counter()
def check(x,msg):
 if not x: raise AssertionError(msg)
def log(s):print(s,flush=True)
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def readlines(p):
 with p.open() as f:
  for line in f:yield json.loads(line)
def exp(v,d):
 check(isinstance(v,(list,tuple)) and len(v)==d and all(type(x)==int and x>=0 for x in v),'bad exponent')
 return tuple(v)
def addto(p,e,c):
 if c:p[e]=p.get(e,0)+c
def clean(p):return {e:c for e,c in p.items() if c}
def mul(p,q):
 out={}
 for e,c in p.items():
  for f,v in q.items():addto(out,tuple(a+b for a,b in zip(e,f)),c*v)
 return clean(out)
def gap(G,k):
 a,b=(4,9) if k==2 else (3,8)
 out={e:a*c for e,c in mul(G[k],G[k]).items()}
 for e,c in mul(G[k-1],G[k+1]).items():addto(out,e,-b*c)
 return clean(out)
def parse_poly(data,d):
 p={}
 for e,c in data:
  e=exp(e,d);check(type(c)==int and c!=0 and e not in p,'bad target term');p[e]=c
 return p
def key(p,d):return (d,tuple(sorted(p.items())))
inputs=['a3_polynomials.jsonl','a3_unique_gamma.jsonl','a3_gamma_aliases.json','coefficient_certificates.json','normalized_faces.jsonl','face_aliases.json','certificates.jsonl']
hashes={name:digest(D/name) for name in inputs}
# Verify all exact identities before using any normalized target.
targets=[];target_keys=set();dims=[];minimum_weight=None
for r,cert in zip_longest(readlines(D/'normalized_faces.jsonl'),readlines(D/'certificates.jsonl')):
 check(r is not None and cert is not None,'unequal target/certificate lengths')
 pid=len(targets);check(r['id']==cert['id']==pid,'target/certificate ID mismatch')
 d=r['variables'];check(type(d)==int and 1<=d<=7,'bad dimension');p=parse_poly(r['polynomial'],d)
 check(p and max(map(sum,p))<=6 and gcd(*p.values())==1,'invalid primitive target')
 K=key(p,d);check(K not in target_keys,'duplicate target');target_keys.add(K);targets.append(K);dims.append(d)
 kind=cert['kind'];check(kind in ('binomial','general'),'unknown square kind');out={}
 terms=cert['terms'];check(set(terms)=={'squares','monomials'},'unexpected identity fields')
 for weight,spec in terms['squares']:
  w=Fraction(weight);check(w>0,'nonpositive square weight');minimum_weight=w if minimum_weight is None else min(minimum_weight,w)
  root={}
  if kind=='binomial':
   check(len(spec)==5,'bad binomial square');m,a,b,u,v=spec;m=exp(m,d);a=exp(a,d);b=exp(b,d)
   addto(root,a,Fraction(u));addto(root,b,-Fraction(v))
  else:
   check(len(spec)==2,'bad general square');m,pairs=spec;m=exp(m,d)
   for e,c in pairs:
    e=exp(e,d);check(e not in root,'duplicate root term');root[e]=Fraction(c)
   check(root,'empty square root')
  for e,c in mul(clean(root),clean(root)).items():addto(out,tuple(x+y for x,y in zip(m,e)),w*c)
  C[kind+'_squares']+=1
 for e,w in terms['monomials']:
  e=exp(e,d);w=Fraction(w);check(w>0,'nonpositive monomial weight');minimum_weight=w if minimum_weight is None else min(minimum_weight,w);addto(out,e,w);C['positive_monomials']+=1
 check(clean(out)==p,'rational square identity mismatch '+str(pid));C[kind+'_identities']+=1
 if (pid+1)%5000==0:log(f'Identities checked {pid+1}; elapsed {time.time()-START:.1f}s')
check(len(targets)==53722,'target count');log('PASS all 53,722 exact rational identities')
# Keep exact polynomial tuples rather than hashes for all subsequent comparisons.
aliases={}
for r in json.loads((D/'face_aliases.json').read_text()):
 k=(r['id'],r['gap'],r['face']);check(k not in aliases,'duplicate alias');check(all(type(x)==int for x in k),'bad alias indices')
 check(0<=k[0]<3437 and k[1] in (2,3) and k[2]>=0,'alias domain')
 pid=r['polynomial'];check(type(pid)==int and 0<=pid<len(targets),'alias target');check(type(r['scale'])==int and r['scale']>0,'alias scale')
 perm=r['permutation'];check(isinstance(perm,list) and len(perm)==dims[pid] and len(perm)==len(set(perm)) and all(type(i)==int and i>=0 for i in perm),'alias permutation')
 aliases[k]=r
check(len(aliases)==63917,'alias count')
advertised={}
for r in json.loads((D/'coefficient_certificates.json').read_text()):
 k=(r['variables'],r['gap']);check(k not in advertised and 1<=k[0]<=7 and k[1] in (2,3),'coefficient group')
 B=r['binomial_positive_ids'];F=r['all_faces_coefficient_positive_ids'];check(len(B)==len(set(B)) and len(F)==len(set(F)) and not(set(B)&set(F)),'coefficient duplicate')
 advertised[k]=(set(B),set(F))
# Univariate falling factors are constructed directly, not imported transform tables.
FALL=[]
for n in range(4):
 a=[1]
 for j in range(n):
  b=[0]*(len(a)+1)
  for i,c in enumerate(a):b[i]-=j*c;b[i+1]+=c
  a=b
 FALL.append(a)
@lru_cache(None)
def six_basis(q):
 denom=1
 for n in q:denom*=factorial(n)
 check(6%denom==0,'factorial denominator')
 out={}
 for e in product(*(range(n+1) for n in q)):
  c=6//denom
  for n,j in zip(q,e):c*=FALL[n][j]
  if c:out[e]=c
 return out
# Monomial-to-binomial coefficients are direct finite differences at zero.
DIFF={(n,k):sum((-1)**(k-j)*comb(k,j)*j**n for j in range(k+1)) for n in range(7) for k in range(n+1)}
@lru_cache(None)
def newton_column(e):
 out=[]
 for f in product(*(range(n+1) for n in e)):
  c=1
  for n,k in zip(e,f):c*=DIFF[n,k]
  if c:out.append((f,c))
 return out
@lru_cache(None)
def shift_column(e):
 return [(f,__import__('math').prod(comb(n,k) for n,k in zip(e,f))) for f in product(*(range(n+1) for n in e))]
def newton(P):
 out={}
 for e,c in P.items():
  for f,a in newton_column(e):addto(out,f,c*a)
 return clean(out)
def face(P,mask,d):
 active=[j for j in range(d) if mask>>j&1];out={}
 for e,c in P.items():
  if any(e[j] for j in range(d) if not(mask>>j&1)):continue
  ee=tuple(e[j] for j in active)
  for f,a in shift_column(ee):addto(out,f,c*a)
 return clean(out)
# Validate each univariate finite-difference column at enough points to determine
# its degree<=6 polynomial identically, independently of any Stirling recurrence.
for n in range(7):
 for x in range(7):check(sum(DIFF[n,k]*comb(x,k) for k in range(n+1) if k<=x)==x**n,'finite difference transform')
used_alias=set();used_target=set();computed={k:(set(),set()) for k in advertised};seen_gamma=[];total_faces=0
with (O/'positivity_coverage.jsonl').open('w') as ledger:
 for r in readlines(D/'a3_unique_gamma.jsonl'):
  rid=r['id'];check(rid==len(seen_gamma),'gamma ID order');d=len(r['types']);Q=[tuple(q) for q in r['quota']]
  check(len(Q)==len(set(Q))==comb(d+3,3) and all(len(q)==d and all(type(v)==int and v>=0 for v in q) and sum(q)<=3 for q in Q),'quota domain')
  gg=r['gamma'];check(len(gg)==5 and all(len(row)==len(Q) for row in gg),'gamma shape')
  G=[]
  for row in gg:
   P={}
   for c,q in zip(row,Q):
    check(type(c)==int and c>=0,'gamma entry')
    if c:
     for e,a in six_basis(q).items():addto(P,e,c*a)
   G.append(clean(P))
  check(G[0]=={(0,)*d:6},'gamma0');seen_gamma.append((d,rid))
  for k in (2,3):
   group=(d,k);check(group in advertised,'missing coefficient group');P=gap(G,k);check(all(sum(e)<=2*k for e in P),'gap degree')
   result={'id':rid,'gap':k,'variables':d};total_faces+=1<<d
   B=newton(P)
   if all(c>=0 for c in B.values()):
    computed[group][0].add(rid);result['certificate']='nonnegative_binomial_coefficients';C['binomial_gap_inputs']+=1
    check(not any((rid,k,mask) in aliases for mask in range(1<<d)),'alias on binomial-certified gap')
   else:
    has_sos=False;results=[]
    for mask in range(1<<d):
     F=face(P,mask,d);kk=(rid,k,mask)
     if all(c>=0 for c in F.values()):
      check(kk not in aliases,'alias on coefficient-positive face');C['coefficient_positive_faces']+=1;results.append({'face':mask,'certificate':'nonnegative_coefficients'});continue
     has_sos=True;check(kk in aliases,'UNCOVERED face '+str(kk));a=aliases[kk];nactive=mask.bit_count();perm=a['permutation'];check(all(j<nactive for j in perm),'out-of-range permutation')
     omitted=set(range(nactive))-set(perm);check(all(all(e[j]==0 for j in omitted) for e in F),'dropped used variable')
     scale=gcd(*F.values());check(scale==a['scale'] and scale>0,'incorrect face gcd');normalized={}
     for e,c in F.items():
      ee=tuple(e[j] for j in perm);check(ee not in normalized,'collapsed distinct face terms');normalized[ee]=c//scale
     check(key(normalized,len(perm))==targets[a['polynomial']],'face-target identity mismatch '+str(kk))
     used_alias.add(kk);used_target.add(a['polynomial']);C['sos_faces']+=1;results.append({'face':mask,'target':a['polynomial'],'scale':scale,'permutation':perm})
    if not has_sos:computed[group][1].add(rid);C['all_faces_coefficient_positive_inputs']+=1
    else:C['sos_gap_inputs']+=1
    result['faces']=results
   ledger.write(json.dumps(result,separators=(',',':'))+'\n')
  if (rid+1)%250==0:log(f'Both gap families checked {rid+1}/3437; elapsed {time.time()-START:.1f}s')
check(len(seen_gamma)==3437,'gamma count');check(used_alias==set(aliases),'unconsumed/extraneous aliases');check(used_target==set(range(len(targets))),'unreferenced targets')
check(computed==advertised,'coefficient classification differs from recomputation')
check(hashes=={name:digest(D/name) for name in inputs},'inputs changed during audit')
receipt={'verdict':'all-population positivity and complete face coverage passed','unique_gamma_inputs':3437,'gap_inputs':6874,'normalized_targets':len(targets),'aliases':len(aliases),'all_integer_population_faces_covered':total_faces,'counters':dict(C),'minimum_positive_weight':str(minimum_weight),'seconds':time.time()-START,'input_sha256':hashes,'audit_code_sha256':digest(Path(__file__)),'coverage_ledger_sha256':digest(O/'positivity_coverage.jsonl'),'scope':'nonnegative integer clone populations; 0/(1+y) faces cover integers, not all real populations between zero and one'}
(O/'positivity_audit.json').write_text(json.dumps(receipt,indent=2)+'\n');log(json.dumps(receipt,indent=2))
