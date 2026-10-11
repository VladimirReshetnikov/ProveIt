"""Build the bounded full-Cayley image and test an enlarged S6 row family.
A modular result is a search diagnostic until an exact rational certificate closes.
"""
from pathlib import Path
from fractions import Fraction as Q
from collections import defaultdict
from itertools import product
from functools import lru_cache
import hashlib,json,pickle,sys,time
sys.dont_write_bytecode=True
B=Path(__file__).resolve().parents[1];V=B/'verification';C=B.parent/'reports/stieltjes-harmonic-resonance/continuations/exact-resonant-identities/certificates/cayley';sys.path.insert(0,str(C/'code'))
import verify_complete_cayley as M
P,R=M.P,M.R;prime=2147483647
for name,digest in M.EXPECTED_SHA256.items():assert hashlib.sha256((C/name).read_bytes()).hexdigest()==digest
coords=[w for w in product(range(5),repeat=7) if P.admissible(w) and P.depth(w)<=4 and P.parity(w)];index={w:i for i,w in enumerate(coords)}
images=[];trace=Q(0);started=time.monotonic()
for i,w in enumerate(coords):
 p=P.projection(w);assert all(t in index for t in p);images.append({index[t]:Q(c) for t,c in p.items()});trace+=Q(p.get(w,0))
 if (i+1)%500==0:print('Projector images',i+1,'/',len(coords),flush=True)
assert trace.denominator==1
print('Exact formal full-Cayley image dimension:',int(trace),flush=True)
(V/'.scratch-real-orders/S6-projector-images.pkl').write_bytes(pickle.dumps(dict(coords=coords,images=images,trace=trace,source_code_sha256=M.EXPECTED_SHA256),protocol=5))
family,counts=R.complete_family();rows=sorted(family);print('Inherited rows:',len(rows),counts,flush=True)
@lru_cache(None)
def inv(d):return pow(d,-1,prime)
def mod(c):c=Q(c);return c.numerator*inv(c.denominator)%prime
modimages=[{i:mod(c) for i,c in row.items() if mod(c)} for row in images]
@lru_cache(None)
def projected_word(w):
 out=defaultdict(int)
 for a,c in M.change_basis(w).items():
  if not P.parity(a):continue  # Explicit conjugation-odd projection.
  cc=mod(c)
  for i,d in modimages[index[a]].items():out[i]=(out[i]+cc*d)%prime
 return {i:c for i,c in out.items() if c}
def projected_raw(row):
 out=defaultdict(int)
 for w,c in row:
  cc=mod(c)
  for i,d in projected_word(w).items():out[i]=(out[i]+cc*d)%prime
 return {i:c for i,c in out.items() if c}
basis={};selected=[]
def insert(row,row_id):
 q=dict(row)
 while q:
  pivot=min(q);a=q[pivot]
  if pivot not in basis:
   scale=inv(a);q={i:c*scale%prime for i,c in q.items()};basis[pivot]=q;selected.append(row_id);return True
  b=basis[pivot]
  for i,c in b.items():
   z=(q.get(i,0)-a*c)%prime
   if z:q[i]=z
   elif i in q:del q[i]
 return False
for j,row in enumerate(rows):
 insert(projected_raw(row),('old',j))
 if (j+1)%500==0:print('Inherited modular elimination',j+1,'rank',len(basis),'stored entries',sum(map(len,basis.values())),flush=True)
old_rank=len(basis)
probe=json.loads((V/'S6-depth-five-escape-probe.json').read_text());newrows=[]
for j,item in enumerate(probe['rows']):
 if 'projected_relation' not in item:continue
 q={index[tuple(t['word'])]:Q(t['coefficient']) for t in item['projected_relation']};newrows.append((j,q));insert({i:mod(c) for i,c in q.items()},('new',j))
target=projected_raw(tuple(R.target().items()));residual=dict(target)
while residual:
 pivot=min(residual)
 if pivot not in basis:break
 a=residual[pivot]
 for i,c in basis[pivot].items():
  z=(residual.get(i,0)-a*c)%prime
  if z:residual[i]=z
  elif i in residual:del residual[i]
cache=dict(prime=prime,coords=coords,images=images,old_rows=rows,new_rows=newrows,selected=selected,target_raw=R.target(),source_code_sha256=M.EXPECTED_SHA256)
(V/'.scratch-real-orders/S6-enlarged-cache.pkl').write_bytes(pickle.dumps(cache,protocol=5))
record=dict(status='SEARCH_DIAGNOSTIC',prime=prime,ambient_bounded_dimension=len(coords),exact_full_Cayley_image_dimension=int(trace),inherited_rows=len(rows),inherited_modular_rank=old_rank,added_rows=len(newrows),enlarged_modular_rank=len(basis),target_modular_residual_terms=len(residual),target_modular_member=not residual,selected_rows=len(selected),elapsed_seconds=round(time.monotonic()-started,3),scope='Exact full-Cayley projector trace in F4, followed by modular row-space search including the 19 bounded depth-five projected escapes. Modular membership is not a rational certificate and does not prove S6; modular nonmembership alone is not a rational nonmembership certificate.')
(V/'S6-enlarged-modular-search.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8');print(json.dumps(record,indent=2),flush=True)
