"""Complete four-vertex core enumeration from all labeled reflexive relations."""
import itertools,json,time
from pathlib import Path
D=Path(__file__).parent

def transitive(rows):
 R=[row|(1<<i) for i,row in enumerate(rows)]
 return all(not(R[j]&~R[i]) for i,row in enumerate(R) for j in range(len(R)) if row>>j&1)
def expand(core,s,types):
 r=list(core)+[0]*len(types)
 for j,t in enumerate(types):
  for a in range(4):
   if t>>a&1:
    if s>>a&1:r[a]|=1<<(4+j)
    else:r[4+j]|=1<<a
 return r

def needs_certificate(core,s,types):
 r=expand(core,s,types);n=len(r);color={}
 for root in range(n):
  if root in color:continue
  color[root]=0;todo=[root];active=0;bip=True
  for v in todo:
   if v>=4:active|=types[v-4]
   for w in range(n):
    if r[v]>>w&1 or r[w]>>v&1:
     if w not in color:color[w]=1-color[v];todo.append(w)
     elif color[w]==color[v]:bip=False
  # A rank-four component must have all four attachment vertices active.
  # With fewer active vertices, their number plus floor((4-active)/2) is ≤3.
  if not bip and active==15:return True
 return False
PERMS=list(itertools.permutations(range(4)))
def canonical(core,s,legal):
 candidates=[]
 for p in PERMS:
  for rev in (False,True):
   rr=tuple(sum(1<<j for j in range(4) if (core[p[j]]>>p[i]&1 if rev else core[p[i]]>>p[j]&1)) for i in range(4))
   ns=sum(1<<j for j in range(4) if bool(s>>p[j]&1)^rev)
   types=sum(1<<sum(1<<j for j in range(4) if t>>p[j]&1) for t in range(1,16) if legal>>t&1)
   candidates.append((rr,ns,types))
 return min(candidates)
start=time.time();edges=[(i,j) for i in range(4) for j in range(4) if i!=j];cores=specs=reduced=retained=0;templates=set()
for bits in range(1<<12):
 core=[sum(1<<j for k,(i,j) in enumerate(edges) if i==v and bits>>k&1) for v in range(4)]
 if not transitive(core):continue
 cores+=1
 for s in range(16):
  types=[t for t in range(1,16) if transitive(expand(core,s,[t,t]))]
  if not types:continue
  assert transitive(expand(core,s,types))
  specs+=1
  if not needs_certificate(core,s,types):reduced+=1;continue
  retained+=1;templates.add(canonical(core,s,sum(1<<t for t in types)))
records=[{'id':i,'core_rows':list(core),'orientation_mask':s,'types':[t for t in range(1,16) if legal>>t&1]} for i,(core,s,legal) in enumerate(sorted(templates))]
(D/'templates.json').write_text(json.dumps(records,indent=2)+'\n')
with(D/'templates.tsv').open('w') as f:
 for r in records:f.write(' '.join(map(str,[r['id'],*r['core_rows'],r['orientation_mask'],len(r['types']),*r['types']]))+'\n')
from collections import Counter
result={'labeled_preorders':cores,'legal_specifications':specs,'structurally_reduced':reduced,'retained':retained,'canonical_templates':len(records),'type_counts':dict(Counter(len(r['types']) for r in records)),'seconds':time.time()-start}
(D/'enumeration.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
