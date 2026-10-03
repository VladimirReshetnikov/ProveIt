"""Independent template coverage and Hall-support audit."""
import json,itertools,math
from pathlib import Path
import sympy as s
D=Path(__file__).parent;R=json.loads((D/'cover3_seventeen_templates.json').read_text())
def trans(rows):
 return all(not(rows[j]&~rows[i])for i,r in enumerate(rows)for j in range(len(rows))if r>>j&1)
def key(core,signs,types):
 keys=[]
 for p in itertools.permutations(range(3)):
  for rev in (False,True):
   es=tuple(sorted((p[j],p[i])if rev else(p[i],p[j])for i,j in core))
   ss=[0]*3
   for i in range(3):ss[p[i]]=signs[i]*(-1 if rev else 1)
   ts=tuple(sorted(sum(1<<p[i]for i in range(3)if t>>i&1)for t in types))
   keys.append((es,tuple(ss),ts))
 return min(keys)
def independent_types(core,signs):
 out=[]
 for t in range(1,8):
  rows=[1<<i for i in range(4)]
  for i,j in core:rows[i]|=1<<j
  for i in range(3):
   if t>>i&1:
    if signs[i]==-1:rows[i]|=8
    else:rows[3]|=1<<i
  if trans(rows):out.append(t)
 return out
classes=set();labeled=0;pc=0
for mask in range(64):
 es=[(i,j)for i in range(3)for j in range(3)if i!=j];core={e for b,e in enumerate(es)if mask>>b&1};rows=[1<<i for i in range(3)]
 for i,j in core:rows[i]|=1<<j
 if not trans(rows):continue
 pc+=1
 for signs in itertools.product((-1,1),repeat=3):
  types=independent_types(core,signs)
  # Rank3 requires each core vertex to have an exterior neighbor. If each
  # has one allowable type, sufficient copies supply a disjoint 3-matching.
  if not all(any(t>>i&1 for t in types)for i in range(3)):continue
  labeled+=1;classes.add(key(core,signs,types))
expected={key(r['core_arcs'],r['signs'],r['types'])for r in R}
assert pc==29 and labeled==130 and len(classes)==17
assert classes==expected and len(R)==len(expected)
print('Independent complete coverage: 29 cores, 130 signed templates, 17 classes',flush=True)

def quotas(d,total):
 if d==0:
  if total==0:yield ()
 else:
  for k in range(total+1):
   for q in quotas(d-1,total-k):yield(k,)+q
for r in R:
 types=r['types'];d=len(types);g=[{}for _ in range(4)]
 for total in range(4):
  for q in quotas(d,total):
   ext=[t for t,c in zip(types,q)for _ in range(c)];N=3+total;rows=[0]*N
   for i,j in r['core_arcs']:rows[i]|=1<<j
   for j,t in enumerate(ext,3):
    for i in range(3):
     if t>>i&1:
      if r['signs'][i]==-1:rows[i]|=1<<j
      else:rows[j]|=1<<i
   counts=[0]*4
   for A in range(1<<N):
    k=A.bit_count()
    if k>3:continue
    for B in range(1<<N):
     if A&B or B.bit_count()!=k or ((A|B)>>3)!=(1<<total)-1:continue
     sub=A;feasible=True
     while sub:
      union=0
      for i in range(N):
       if sub>>i&1:union|=rows[i]
      if (union&B).bit_count()<sub.bit_count():feasible=False;break
      sub=(sub-1)&A
     if feasible:counts[k]+=1
   for k,c in enumerate(counts):
    if c:g[k][q]=c
 expected=[{tuple(q):c for q,c in gg}for gg in r['gamma_binomial']]
 assert g==expected,r['id']
 xs=s.symbols(' '.join('n'+str(t)for t in types),seq=True)
 polys=[s.expand(sum(c*s.prod(s.prod(x-j for j in range(a))/math.factorial(a)for x,a in zip(xs,q))for q,c in gg.items()))for gg in g]
 assert all(s.expand(p-s.sympify(q))==0 for p,q in zip(polys,r['gamma_monomial']))
 assert s.expand(polys[2]**2-3*polys[1]*polys[3]-s.sympify(r['gap_monomial']))==0
 print('Independent Hall polynomial/gap verified',r['id'],flush=True)
# Complete face partition and exponent-domain checks omitted by older verifiers.
for i in [2,4,5,6,7,8,12,14]:
 data=json.loads((D/f'cover3_sos_{i}.json').read_text());faces=data['certified_faces'];failed=data['failed_masks'];masks=[f['mask']for f in faces];n=len(R[i]['types'])
 assert len(set(masks))==len(masks) and len(set(failed))==len(failed)
 assert set(masks).isdisjoint(failed) and set(masks)|set(failed)==set(range(1<<n))
 for f in faces:
  dim=f['mask'].bit_count()
  for weight,poly in f['terms']:
   assert len({tuple(e)for e,v in poly})==len(poly)
   for e,v in poly:assert len(e)==dim and all(isinstance(a,int)and a>=0 for a in e)
 if i not in [2,4,7]:assert not failed
 if i==2:assert failed==[6]
for i,filename in [(4,'cover3_sdp_4.json'),(7,'cover3_sdp_7_complete.json')]:
 faces=json.loads((D/filename).read_text());old=json.loads((D/f'cover3_sos_{i}.json').read_text())
 assert sorted(f['mask']for f in faces)==sorted(old['failed_masks'])
 for f in faces:
  dim=f['mask'].bit_count()
  for weight,poly,meta in f['terms']:
   assert len({tuple(e)for e,v in poly})==len(poly)
   for e,v in poly:assert len(e)==dim and all(isinstance(a,int)and a>=0 for a in e)
   if meta is not None:
    m,z=meta;assert len(m)==dim and all(isinstance(a,int)and a>=0 for a in m)
    assert len({tuple(e)for e,v in z})==len(z)
    for e,v in z:assert len(e)==dim and all(isinstance(a,int)and a>=0 for a in e)
print('All required SOS/SDP face masks and exponent domains fully verified',flush=True)
