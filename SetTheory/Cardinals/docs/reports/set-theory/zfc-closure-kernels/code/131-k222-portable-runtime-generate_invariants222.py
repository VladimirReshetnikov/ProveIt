#!/usr/bin/env python3
"""Fresh exact K224-source bucket fixed point; no CP/GIC masks are loaded."""
from pathlib import Path
from collections import deque, Counter
import json, hashlib, sys
ROOT=Path(__file__).resolve().parent;H=Path(sys.argv[1]).resolve()if len(sys.argv)>1 else ROOT/'results';H.mkdir(parents=True,exist_ok=True);W=ROOT
SOURCES=[H/'sites.json']*2
SEED=[3,0,0,0,3,0,0,0,0]
def need(v,m):
 if not v:raise ValueError(m)
def graph(rows):
 ordered=sorted(rows); leaves={p:i for i,(p,o,r) in enumerate(ordered)};mx=max(map(len,leaves))
 need(len(leaves)==len(rows)==4744,'site count')
 prefixes={p[:k]for p in leaves for k in range(len(p))}
 need(not(set(leaves)&prefixes),'prefix-free');need(all(p+c in prefixes or p+c in leaves for p in prefixes for c in '01'),'full tree')
 def locate(p):
  word=p+'0'*mx
  for k in range(1,mx+1):
   if word[:k] in leaves:return leaves[word[:k]]
  raise ValueError('locate')
 def inc(p):return format((int(p,2)+1)%(1<<len(p)),'0'+str(len(p))+'b')if p else ''
 def cut(p,c,k):
  if k==0:return p
  pos=[i for i,b in enumerate(p)if b==c]
  return p[:pos[-k]]if len(pos)>=k else ''
 g=[]
 for p,o,r in ordered:
  if o=='CI':g.append(['INC',r,locate(inc(p))])
  elif o=='CD':g.append(['DEC',r,locate(inc(p)),locate(inc(cut(p,'0',1)))])
  elif o=='CB':g.append(['JUMP',locate(inc(cut(p,'0',r)))])
  elif o=='CC':g.append(['JUMP',locate(cut(p,'1',r))])
  else:need(o=='CH'and r is None,'opcode');g.append(['HALT'])
 return ordered,g,locate('')
def main():
 ordered,G,initial=graph(json.loads(SOURCES[0].read_text())); ordered6,G6,i6=graph(json.loads(SOURCES[1].read_text()))
 need(G==G6 and initial==i6,'shared source CFG');need([a[1:]for a in ordered]==[a[1:]for a in ordered6],'ordered opcode agreement')
 B=[None]*len(G);B[initial]=tuple(1<<v for v in SEED);q=deque([initial]);queued={initial};updates=0
 def shift(mask,delta):
  out=0
  for v in range(9):
   if mask>>v&1:
    if delta==1:out|=1<<min(8,v+1)
    elif v==8:out|=384
    elif v>0:out|=1<<(v-1)
  return out
 def edges(i):
  ins=G[i];v=B[i]
  if ins[0]=='HALT':return []
  if ins[0]=='JUMP':return [(ins[1],v)]
  r=ins[1];out=[]
  if ins[0]=='INC':w=list(v);w[r]=shift(v[r],1);return[(ins[2],tuple(w))]
  if v[r]&1:w=list(v);w[r]=1;out.append((ins[3],tuple(w)))
  if v[r]&~1:w=list(v);w[r]=shift(v[r]&~1,-1);out.append((ins[2],tuple(w)))
  return out
 while q:
  i=q.popleft();queued.remove(i)
  for j,v in edges(i):
   new=v if B[j] is None else tuple(a|b for a,b in zip(B[j],v))
   if new!=B[j]:
    B[j]=new;updates+=1
    if j not in queued:q.append(j);queued.add(j)
 one=[]
 for i,ins in enumerate(G):
  if B[i] is not None and ins[0]=='DEC':
   mask=B[i][ins[1]]
   if mask==1 or not mask&1:one.append(dict(site=i,paths=[ordered[i][0],ordered6[i][0]],register=ins[1],only='zero'if mask==1 else 'positive',mask=mask))
 out=dict(status='FRESH_K_BUCKET_FIXED_POINT',threshold=8,seed=SEED,initial_site=initial,site_count=len(G),graph=G,ordered=ordered,ordered06=ordered6,states=B,updates=updates,one_sided_decrements=one,unreachable_sites=[i for i,b in enumerate(B)if b is None],source_files=['inputs/sites.json']*2,source_sha256=[hashlib.sha256(p.read_bytes()).hexdigest()for p in SOURCES],scope='Universal reachable-source restriction; not a runtime-window certificate.')
 (H/'invariants.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
 (H/'masks.txt').write_text(''.join(' '.join(map(str,b or [0]*9))+'\n'for b in B))
 for name,ss in [('01',ordered),('06',ordered6)]:
  (H/f'sites{name}.txt').write_text(''.join(f'{p} {o} {0 if r is None else r}\n'for p,o,r in ss))
 summary=dict(updates=updates,reachable_overapprox=sum(b is not None for b in B),unreachable_sites=out['unreachable_sites'],one_sided_decrements=one,constant_slots=sum(m>0 and m&(m-1)==0 and m!=256 for b in B if b for m in b),mask_distribution=Counter(str(m)for b in B if b for m in b))
 (H/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
if __name__=='__main__':main()
