#!/usr/bin/env python3
"""Independent exact audit of symmetry-averaged binomial-basis square identities.
Uses subset-union enumeration for multiplication. No producer module imports.
Certifies global integer-population gaps, not fractional-real population gaps.
"""
from pathlib import Path
from fractions import Fraction
from functools import lru_cache
from collections import Counter
import argparse,json,hashlib,time
D=Path('/workspace/shared/preorder-gamma-degree4/four-attachment');O=Path(__file__).parent
parser=argparse.ArgumentParser();parser.add_argument('certificates',type=Path,nargs='+');args=parser.parse_args();start=time.time()
def ck(ok,msg):
 if not ok:raise AssertionError(msg)
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def add(p,e,c):
 if c:p[e]=p.get(e,0)+c
def clean(p):return {e:c for e,c in p.items() if c}
def degree(q,d=15):return sum((q>>(3*i))&7 for i in range(d))
def valid(q,d):ck(type(q)==int and 0<=q<(1<<(3*d)),'invalid packed exponent')
@lru_cache(None)
def weight(a,b):
 out=[]
 for t in range(max(a,b),a+b+1):
  count=0
  for A in range(1<<t):
   if A.bit_count()!=a:continue
   for B in range(1<<t):
    if B.bit_count()==b and (A|B)==(1<<t)-1:count+=1
  if count:out.append((t,count))
 return out
@lru_cache(None)
def column(a,b,d):
 out={0:1}
 for i in range(d):
  aa=(a>>(3*i))&7;bb=(b>>(3*i))&7
  ck(aa+bb<8,'packed multiplication carry risk')
  if not(aa or bb):continue
  new={}
  for code,c in out.items():
   for t,w in weight(aa,bb):new[code|(t<<(3*i))]=c*w
  out=new
 return tuple(out.items())
def mul(P,Q,d):
 R={}
 for a,u in P.items():
  for b,v in Q.items():
   for e,w in column(a,b,d):add(R,e,u*v*w)
 return clean(R)
@lru_cache(None)
def image(code,action):
 out=0
 for i,j in enumerate(action):out|=((code>>(3*i))&7)<<(3*j)
 return out
files=[D/'a4_gaps.jsonl',D/'face_orbits.json',D/'face_tasks.tsv',*args.certificates];hashes={str(p):digest(p) for p in files}
G={r['id']:r for r in map(json.loads,(D/'a4_gaps.jsonl').read_text().splitlines())};F=json.loads((D/'face_orbits.json').read_text());tasks=[tuple(map(int,l.split())) for l in (D/'face_tasks.tsv').read_text().splitlines()]
prior=json.loads((O/'face_orbit_audit.json').read_text())
for name in ['a4_gaps.jsonl','face_orbits.json','face_tasks.tsv']:ck(prior['input_sha256'][name]==digest(D/name),'changed approved input')
receipts=[];seen=set()
for path in args.certificates:
 r=json.loads(path.read_text());tid,k=r['template'],r['gap'];ck((tid,k) not in seen,'duplicate global certificate');seen.add((tid,k));ck(tid in G and k in (2,3),'certificate target domain');d=G[tid]['variables'];target=dict(G[tid]['gap'+str(k)]);ck(len(target)==len(G[tid]['gap'+str(k)]),'duplicate target terms')
 actions=[tuple(a['variable_map']) for a in F[tid]['actions']];ck(len(actions)==len(set(actions)) and all(sorted(a)==list(range(d)) for a in actions),'invalid averaging actions')
 # Invariance is also verified here on the exact target gap, not assumed.
 for a in actions:ck({image(e,a):c for e,c in target.items()}==target,'target gap not action-invariant')
 cert=r['certificate'];ck(set(cert)=={'squares','positive_binomial_remainder'},'unknown certificate fields');result={};cnt=Counter();minweight=None
 for w,rr in cert['squares']:
  w=Fraction(w);ck(w>0,'nonpositive square coefficient');minweight=w if minweight is None else min(minweight,w);ck(len(rr)==2,'bad square record');m,pairs=rr;valid(m,d);root={}
  for q,c in pairs:valid(q,d);ck(q not in root,'duplicate root binomial');root[q]=Fraction(c)
  ck(root and all(root.values()),'empty or zero-term root');ck(degree(m,d)+2*max(degree(q,d) for q in root)<=2*k,'ray exceeds target degree')
  ray=mul({m:Fraction(1)},mul(root,root,d),d)
  # Expand every action image before averaging; no orbit-aggregated LP residual.
  for a in actions:
   for q,c in ray.items():add(result,image(q,a),w*c/len(actions))
  cnt['positive_square_orbits']+=1;cnt['individual_square_images']+=len(actions)
 for q,c in cert['positive_binomial_remainder']:
  valid(q,d);c=Fraction(c);ck(c>=0,'negative binomial remainder');add(result,q,c);cnt['nonnegative_binomial_remainders']+=1
 ck(clean(result)==target,'FULL COEFFICIENT IDENTITY FAILED '+str((tid,k)))
 covered=[t for t in tasks if t[:2]==(tid,k)]
 receipt={'template':tid,'gap':k,'variables':d,'group_order':len(actions),'identity':'unscaled gap = positive weighted group-averaged B_m*(sum c_q B_q)^2 + nonnegative binomial remainder','counts':dict(cnt),'target_coefficients':len(target),'minimum_square_weight':str(minweight),'previous_outstanding_face_tasks_covered':len(covered),'covered_face_masks':[m for _,_,m in covered]}
 receipts.append(receipt);print('PASS global integer gap',tid,k,'square orbits',cnt['positive_square_orbits'],'face tasks covered',len(covered),flush=True)
ck(hashes=={str(p):digest(p) for p in files},'inputs changed during verification')
receipt={'verdict':'listed global integer-population gaps approved; other gaps remain pending','identities':receipts,'total_outstanding_face_tasks_covered':sum(r['previous_outstanding_face_tasks_covered'] for r in receipts),'seconds':time.time()-start,'input_sha256':hashes,'audit_code_sha256':digest(Path(__file__)),'scope':'integer populations n_i>=0; B_m multipliers need not be nonnegative at fractional n_i'}
(O/'global_binomial_square_audit.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:v for k,v in receipt.items() if k not in ('input_sha256','identities')},indent=2),flush=True)
