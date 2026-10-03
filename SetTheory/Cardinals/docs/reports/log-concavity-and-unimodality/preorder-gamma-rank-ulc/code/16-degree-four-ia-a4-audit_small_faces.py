#!/usr/bin/env python3
"""Independent incremental a4 positivity audit for selected complete templates.
Rebuilds gaps from gamma, exact 720-scaled shifted faces, both alias stages and
rational identities. A template passes only if every outstanding orbit task does.
Use --certificates PATH only on an immutable completed certificate snapshot.
"""
import argparse,json,hashlib,time
from pathlib import Path
from fractions import Fraction
from itertools import product
from functools import lru_cache
from collections import Counter
from math import factorial,comb,gcd
D=Path('/workspace/shared/preorder-gamma-degree4/four-attachment');S=D/'small-faces';O=Path(__file__).parent
A=argparse.ArgumentParser();A.add_argument('--certificates',type=Path);args=A.parse_args();START=time.time()
def ck(ok,msg):
 if not ok:raise AssertionError(msg)
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def records(p):
 with p.open() as f:
  for line in f:yield json.loads(line)
def add(p,e,c):
 if c:p[e]=p.get(e,0)+c
def clean(p):return {e:c for e,c in p.items() if c}
def mul(P,Q):
 R={}
 for e,a in P.items():
  for f,b in Q.items():add(R,tuple(x+y for x,y in zip(e,f)),a*b)
 return clean(R)
def ex(e,d):
 ck(isinstance(e,(list,tuple)) and len(e)==d and all(type(x)==int and x>=0 for x in e),'bad exponent');return tuple(e)
def pairs(data,d):
 R={}
 for e,c in data:
  e=ex(e,d);ck(type(c)==int and c and e not in R,'bad polynomial term');R[e]=c
 return R
files=[D/'templates.json',D/'a4_polynomials.jsonl',D/'a4_gaps.jsonl',D/'face_tasks.tsv',D/'face_orbits.json',S/'selection.json',S/'source_faces.jsonl',S/'normalized_faces.jsonl',S/'face_aliases.json']
if args.certificates:files.append(args.certificates)
hashes={str(p.relative_to(D)) if p.is_relative_to(D) else str(p):digest(p) for p in files}
# Reuse only approved-data hashes, never the producer's transformations.
prior=json.loads((O/'face_orbit_audit.json').read_text())
for f in ['templates.json','a4_polynomials.jsonl','a4_gaps.jsonl','face_tasks.tsv','face_orbits.json']:ck(prior['input_sha256'][f]==digest(D/f),'changed previously audited input '+f)
T=json.loads((D/'templates.json').read_text());G=list(records(D/'a4_polynomials.jsonl'));selection=json.loads((S/'selection.json').read_text())
selected=[r['id'] for r in T if len(r['types'])<=5];ck(selection['templates']==selected and len(selected)==33,'selection mismatch')
tasks=[tuple(map(int,line.split())) for line in (D/'face_tasks.tsv').read_text().splitlines()];ck(len(tasks)==len(set(tasks))==39367,'task domain');tasks=sorted(tasks)
source_expected={i:task for i,task in enumerate(tasks) if task[0] in selected};ck(selection['source_face_targets']==list(source_expected),'source IDs selection mismatch');ck(len(source_expected)==303,'selected task count')
FALL=[]
for n in range(5):
 p=[1]
 for j in range(n):
  q=[0]*(len(p)+1)
  for i,c in enumerate(p):q[i]-=j*c;q[i+1]+=c
  p=q
 FALL.append(p)
@lru_cache(None)
def basis24(q):
 den=1
 for x in q:den*=factorial(x)
 ck(24%den==0,'gamma denominator')
 P={}
 for e in product(*(range(x+1) for x in q)):
  c=24//den
  for n,j in zip(q,e):c*=FALL[n][j]
  if c:P[e]=c
 return P
@lru_cache(None)
def shifted(e):
 out=[]
 for f in product(*(range(x+1) for x in e)):
  c=1
  for n,k in zip(e,f):c*=comb(n,k)
  out.append((f,c))
 return out

def face720(P,mask,d):
 R={}
 for e,c in P.items():
  if any(e[j] for j in range(d) if not(mask>>j&1)):continue
  for f,a in shifted(e):add(R,f,c*a)
 R=clean(R);ck(all(c%4==0 for c in R.values()),'720 denominator not cleared')
 return {e:5*(c//4) for e,c in R.items()}
# G_k=24 gamma_k, so their Newton gap is 576 times the original gap.
reconstructed={}
for tid in selected:
 r=G[tid];d=len(r['types']);Q=list(map(tuple,r['quota']));polys=[]
 for row in r['gamma']:
  P={}
  for q,c in zip(Q,row):
   if c:
    for e,a in basis24(q).items():add(P,e,c*a)
  polys.append(clean(P))
 ck(polys[0]=={(0,)*d:24},'gamma zero')
 for k,left,right in [(2,4,9),(3,3,8)]:
  P={e:left*c for e,c in mul(polys[k],polys[k]).items()}
  for e,c in mul(polys[k-1],polys[k+1]).items():add(P,e,-right*c)
  reconstructed[tid,k]=clean(P)
sources={};source_polys={}
for r in records(S/'source_faces.jsonl'):
 sid=r['id'];ck(sid in source_expected and sid not in sources,'bad source ID');task=(r['template'],r['gap'],r['face']);ck(task==source_expected[sid],'source task mapping mismatch')
 tid,k,mask=task;d=len(T[tid]['types']);F=face720(reconstructed[tid,k],mask,d);ck(any(c<0 for c in F.values()),'source face already coefficient-positive')
 coords=[j for j in range(d) if any(e[j] for e in F)];ck(r['coordinates']==coords and r['variables']==len(coords),'source coordinate compression mismatch')
 factor=gcd(*F.values());ck(factor==r['divisor'] and factor>0,'source gcd divisor mismatch');expected={tuple(e[j] for j in coords):c//factor for e,c in F.items()};actual=pairs(r['polynomial'],len(coords));ck(actual==expected,'source polynomial differs from reconstructed gamma gap')
 sources[sid]=r;source_polys[sid]=actual
ck(set(sources)==set(source_expected),'uncovered source tasks')
normalized={}
for r in records(S/'normalized_faces.jsonl'):
 nid=r['id'];ck(nid==len(normalized),'normalized ID domain');P=pairs(r['polynomial'],r['variables']);ck(gcd(*P.values())==1,'nonprimitive normalized target');normalized[nid]=(r['variables'],P)
ck(len(normalized)==303,'normalized target count')
alias={};used_norm=set()
for r in json.loads((S/'face_aliases.json').read_text()):
 sid=r['id'];ck(sid in sources and sid not in alias,'bad source alias');src=sources[sid];ck((r['gap'],r['face'])==(src['gap'],src['face']),'alias gap/face mismatch')
 nid=r['polynomial'];ck(nid in normalized,'alias target');d,P=normalized[nid];perm=r['permutation'];ck(len(perm)==d and len(set(perm))==len(perm) and all(type(i)==int and 0<=i<src['variables'] for i in perm),'bad alias coordinate permutation')
 missing=set(range(src['variables']))-set(perm);ck(all(all(e[j]==0 for j in missing) for e in source_polys[sid]),'omitted used source variable');scale=r['scale'];ck(type(scale)==int and scale>0,'alias scale')
 transformed={tuple(e[j] for j in perm):c for e,c in source_polys[sid].items()};ck(transformed=={e:scale*c for e,c in P.items()},'source-to-normalized polynomial identity mismatch');ck(gcd(*source_polys[sid].values())==scale,'alias gcd mismatch')
 alias[sid]=r;used_norm.add(nid)
ck(set(alias)==set(sources) and used_norm==set(normalized),'alias/target coverage mismatch')
print('PASS all 303 exact source-face mappings and normalization identities',flush=True)
# Each certificate independently establishes a target's positivity on y>=0.
certified=set();counter=Counter();minweight=None
if args.certificates:
 for cert in records(args.certificates):
  nid=cert['id'];ck(nid in normalized and nid not in certified,'duplicate/extraneous target certificate');terms=cert['terms'];ck(terms is not None,'incomplete certificate in immutable ledger');d,P=normalized[nid];out={}
  for w,data in terms['squares']:
   w=Fraction(w);ck(w>0,'nonpositive square weight');minweight=w if minweight is None else min(minweight,w);root={}
   if len(data)==5:
    m,a,b,u,v=data;m=ex(m,d);add(root,ex(a,d),Fraction(u));add(root,ex(b,d),-Fraction(v));kind='binomial'
   else:
    ck(len(data)==2,'unknown square encoding');m,rr=data;m=ex(m,d);kind='general'
    for e,c in rr:e=ex(e,d);ck(e not in root,'duplicate root exponent');root[e]=Fraction(c)
   if 'kind' in cert:ck(cert['kind']==kind,'certificate kind mismatch')
   for e,c in mul(clean(root),clean(root)).items():add(out,tuple(x+y for x,y in zip(m,e)),w*c)
   counter[kind+'_squares']+=1
  for e,w in terms['monomials']:
   w=Fraction(w);ck(w>0,'nonpositive monomial weight');minweight=w if minweight is None else min(minweight,w);add(out,ex(e,d),w);counter['positive_monomials']+=1
  ck(clean(out)==P,'exact rational identity failed '+str(nid));certified.add(nid);counter['identities']+=1
coverage=[];complete=[]
for tid in selected:
 required={sid for sid,task in source_expected.items() if task[0]==tid};passed={sid for sid in required if alias[sid]['polynomial'] in certified};pending=required-passed
 if not pending:complete.append(tid)
 coverage.append({'template':tid,'outstanding_orbit_tasks':len(required),'certified_tasks':len(passed),'pending_source_ids':sorted(pending),'approved':not pending})
ck(hashes=={str(p.relative_to(D)) if p.is_relative_to(D) else str(p):digest(p) for p in files},'inputs changed during audit')
receipt={'verdict':'complete face mapping approved; template positivity approved exactly for listed complete templates','selected_templates':selected,'source_faces':303,'normalized_targets':303,'certified_targets':len(certified),'approved_complete_templates':complete,'pending_templates':[i for i in selected if i not in complete],'coverage':coverage,'counter':dict(counter),'minimum_weight':str(minweight) if minweight is not None else None,'seconds':time.time()-START,'input_sha256':hashes,'audit_code_sha256':digest(Path(__file__)),'scope':'nonnegative integer clone populations; does not claim positivity of pending templates'}
name='small_faces_incremental_audit.json' if args.certificates else 'small_faces_mapping_audit.json'
(O/name).write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:v for k,v in receipt.items() if k not in ('coverage','input_sha256')},indent=2),flush=True)
