"""Owned generic finite-history patch checker. Standard library only.
A passing result supplies the finite premises of the stated stuttering theorem;
it is not a new Lean/Rocq kernel theorem.
"""

if not __debug__:
    raise RuntimeError("Verification requires enabled assertions; do not use python -O or PYTHONOPTIMIZE.")

from pathlib import Path
import json,hashlib
D=Path(__file__).parent

def table(path):
 T={}
 for line in path.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,r,w,d,n=line.split();q,r,w,n=map(int,(q,r,w,n));assert(q,r)not in T
  assert r in(0,1)and w in(0,1)and d in('L','R');T[q,r]=(w,1 if d=='R'else-1,n)
 return T

def verify(data):
 tables=[table(D/data[x])for x in('old','new')];pins=[hashlib.sha256((D/data[x]).read_bytes()).hexdigest()for x in('old','new')];assert pins==data['sha256']
 A,B=tables;start=data['start'];halt=data['halt'];assert set(A)==set(B)
 assert all((q,b)in A for q,_ in A for b in(0,1));assert halt not in{q for q,b in A}
 states={q for q,b in A};assert start in states
 assert all(z in states|{halt}for T in tables for w,d,z in T.values())
 changed={k for k in A if A[k]!=B[k]};claims=data['blocks'];assert{tuple(c['entry'])for c in claims}==changed
 local=[]
 for c in claims:
  q,b=c['entry'];guard={int(i):v for i,v in c['context'].items()};assert guard[0]==b and all(v in(0,1)for v in guard.values())
  ends=[];traces=[]
  for T,n in zip(tables,c['durations']):
   assert 0<n<=100;state=q;head=0;tape=guard.copy();trace=[]
   for step in range(n):
    assert head in tape,'Opaque exterior read'
    r=tape[head];assert state!=halt
    if step:assert(state,r)not in changed,'Modified strict interior'
    w,d,z=T[state,r];trace.append([state,head,r,w,d,z]);tape[head]=w;state=z;head+=d
   ends.append((state,head,tape));traces.append(trace)
  assert ends[0]==ends[1];local.append(dict(entry=c['entry'],durations=c['durations'],traces=traces,endpoint=ends[0]))
 histories=[]
 for ti,T in enumerate(tables[:1]):
  incoming={}
  for(q,b),(w,d,z)in T.items():incoming.setdefault(z,[]).append((q,b,w,d,z))
  for q,b in sorted(changed):
   depth=int(data['history_depth'][str(q)]);assert depth>=1
   # Every occurrence before depth transitions must be impossible, independently of tape.
   states={start}
   for _ in range(depth):
    assert q not in states,'Uncovered short initial history'
    states={z for u in states for v in(0,1)if(u,v)in T for w,d,z in[T[u,v]]}
   paths=[[]]
   for _ in range(depth):paths=[ [e]+p for p in paths for e in incoming.get(p[0][0]if p else q,[])]
   assert paths
   checked=skipped=0
   for path in paths:
    h=-sum(e[3]for e in path);known={}
    for u,r,w,d,z in path:known[h]=w;h+=d
    assert h==0
    if 0 in known and known[0]!=b:skipped+=1;continue
    known[0]=b
    choices=[c for c in claims if c['entry']==[q,b]and all(known.get(int(i))==v for i,v in c['context'].items())]
    assert choices,('Uncovered reachable history',ti,q,b,path,known)
    checked+=1
   histories.append(dict(table=ti,entry=[q,b],depth=depth,graph_histories=len(paths),covered=checked,read_incompatible=skipped))
 return dict(status='FINITE_PATCH_PREMISES_PASS',states=len(A)//2,changed_rows=len(changed),local_blocks=len(local),histories=histories,local=local,conclusion_scope='Finite premises of positive-duration whole-tape stuttering equivalence from state0 on arbitrary initial tape; no new kernel compilation.')
if __name__=='__main__':
 result=verify(json.load(open(D/'patch.json')));(D/'PATCH_RESULT.json').write_text(json.dumps(result,indent=2));print(json.dumps({k:v for k,v in result.items()if k!='local'},indent=2))
