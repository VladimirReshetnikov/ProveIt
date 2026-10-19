import semantic_fragments as s
import collections,json,time
S=s.SITES;CFG=s.cfg(s.ROOT);K=4;tail=1<<K;full=(1<<(K+1))-1
initial=tuple(1<<min(n,K)for n in (3,0,0,0,3,0,0,0,0))
I={0:initial};queue=collections.deque([0]);queued={0};n=0
while queue:
 q=queue.popleft();queued.remove(q);n+=1;vs=I[q];op,r,pos,zero=CFG[q]
 succ=[]
 if op=='CH':continue
 if op=='CD':
  if vs[r]&1:
   v=list(vs);v[r]=1;succ.append((zero,tuple(v)))
  if vs[r]&~1:
   v=list(vs);v[r]=((v[r]&~1)>>1)|(v[r]&tail);succ.append((pos,tuple(v)))
 else:
  v=list(vs)
  if op=='CI':v[r]=((v[r]<<1)&full)|(v[r]&tail)
  succ.append((pos,tuple(v)))
 for p,v in succ:
  if p==-1:p=0
  old=I.get(p,(0,)*9);new=tuple(a|b for a,b in zip(old,v))
  if old!=new:
   I[p]=new
   if p not in queued:queue.append(p);queued.add(p)
print('flow',n,len(I),sum(op=='CD'and I[i][r]==1 for i,(op,r,*_)in enumerate(CFG)if i in I),flush=True)
bytree=collections.defaultdict(list)
idx={p:i for i,(p,*_)in enumerate(S)}
for p,t in s.NODES.items():bytree[t].append(p)
records=[]
for t,ps in bytree.items():
 if s.info(t)[1]!=(0,0):continue
 rows=s.cfg(t);good=[]
 for p in ps:
  first=p+s.leaves(t)[0][0];i=idx[first]
  if i not in I:continue
  v=I[i];seen=set();q=0
  while q!=-1 and q not in seen:
   seen.add(q);op,r,pos,zero=rows[q]
   if op=='CI'or op=='CH':break
   if op=='CD':
    if v[r]!=1:break
    q=zero
   else:q=pos
  if q==-1:good.append(p)
 if good:records.append(dict(tree=t,leaves=s.info(t)[0],occurrences=len(ps),identity_occurrences=good,all_instances=len(ps)==len(good)))
records.sort(key=lambda x:(not x['all_instances'],-x['leaves']))
Path=__import__('pathlib').Path
Path('zero_specialization.json').write_text(json.dumps(dict(iterations=n,reachable=len(I),identity_fragments=records),indent=2)+'\n')
for x in records:print(x['leaves'],x['occurrences'],len(x['identity_occurrences']),x['all_instances'],x['identity_occurrences'][:5],x['tree'])
