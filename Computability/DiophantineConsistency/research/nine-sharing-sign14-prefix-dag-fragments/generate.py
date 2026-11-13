#!/usr/bin/env python3
"""Split pinned row ASTs at shared-node and short-subtree boundaries."""
import collections,hashlib,json
from pathlib import Path
P=Path(__file__).resolve().parent;src=P.parent/'nine-sharing-sign14-tau-candidate/seed.json'
h=lambda b:hashlib.sha256(b).hexdigest();raw=src.read_bytes();assert h(raw)=='7048a10d409ab5ff8031a444cd32117ba772b3834425c17a066188338e189ea9'
s=json.loads(raw);counts=collections.Counter();sizes={}
def intern(t):
 x=tuple(t) if len(t)==2 else (t[0],intern(t[1]),intern(t[2]));counts[x]+=1;sizes[x]=1 if len(x)==2 else 1+sizes[x[1]]+sizes[x[2]];return x
roots=[intern(r['expr']) for r in s['residuals']];shared=sorted((x for x in counts if counts[x]>=2 and sizes[x]>=9),key=lambda x:(sizes[x],repr(x)));ids={x:i for i,x in enumerate(shared)};assert len(shared)==44
ports={'beta':'B','K0':'K','MC':'C','MF':'F'};ops={'add':'+','sub':'-','mul':'*'}
def enc(t):
 if t[0]=='var':return chr(97+t[1])
 if t[0]=='port':return ports[t[1]]
 if t[0]=='num':return str(t[1])
 return ops[t[0]]+enc(t[1])+enc(t[2])
fragments=[];frag_ids={}
def part(t,self_id=None):
 if t in ids and ids[t]!=self_id:return ['ref',ids[t]]
 b=enc(t).encode('ascii')
 if len(b)<=32:
  if b not in frag_ids:
   n=len(fragments);frag_ids[b]=n;p=P/f'fragment{n:03}.prefix';p.write_bytes(b);fragments.append({'file':p.name,'sha256':h(b),'length':len(b)})
  return ['frag',frag_ids[b]]
 assert t[0] in ops
 return ['op',ops[t[0]],part(t[1]),part(t[2])]
shared_parts=[part(t,i) for i,t in enumerate(shared)];row_parts=[part(t) for t in roots]
def materialize(x,upto):
 if x[0]=='frag':return (P/fragments[x[1]]['file']).read_bytes()
 if x[0]=='ref':assert x[1]<upto;return materialize(shared_parts[x[1]],x[1])
 assert x[0]=='op';return x[1].encode('ascii')+materialize(x[2],upto)+materialize(x[3],upto)
for i,x in enumerate(shared_parts):assert materialize(x,i)==enc(shared[i]).encode()
for i,x in enumerate(row_parts):assert materialize(x,44)==enc(roots[i]).encode()
m={'seed_sha256':h(raw),'fragments':fragments,'shared':shared_parts,'rows':row_parts,'scope':'External decomposition only; no Lean full-file theorem.'}
(P/'manifest.json').write_text(json.dumps(m,sort_keys=True,indent=2)+'\n');print(json.dumps({'status':'GENERATED','fragments':len(fragments),'shared':44,'rows':5},sort_keys=True))
