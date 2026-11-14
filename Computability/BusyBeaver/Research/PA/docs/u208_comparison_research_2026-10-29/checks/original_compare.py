from pathlib import Path
from collections import deque,defaultdict
import hashlib,json
BASE=Path(__file__).resolve().parents[1]
def need(c):
 if not c:raise ValueError("comparison obligation failed")
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def table(p):
 t={}
 for l in p.read_text().splitlines():
  if not l.strip() or l.startswith('#'):continue
  q,b,w,d,r=l.split();k=(int(q),int(b));need(k not in t);t[k]=(int(w),d,int(r))
 need(len(t)==416);need(set(t)=={(q,b) for q,_ in t for b in (0,1)})
 return t

def canon(t):
 states={q for q,b in t};need(len(states)==208)
 halt=set(r for w,d,r in t.values())-states;need(halt=={254});nums={0:0,254:-1};queue=deque([0]);rows=[]
 while queue:
  q=queue.popleft()
  for b in (0,1):
   w,d,r=t[q,b]
   if r not in nums:nums[r]=len(nums)-1;queue.append(r)
   rows.append((nums[q],b,w,d,nums[r]))
 need(set(nums)==states|halt)
 s=json.dumps(rows,separators=(',',':')).encode();return hashlib.sha256(s).hexdigest(),nums
items=[];tables={};classes=defaultdict(list)
for p in sorted((BASE/'intake').rglob('*.native.tm')):
 if 'u208' not in p.name or 'rejected' in str(p):continue
 t=table(p);c,n=canon(t); key=str(p.relative_to(BASE));dense=p.with_name(p.name.replace('.native','.'));dense=Path(str(dense).replace('..','.'))
 item={'path':key,'native_sha256':h(p),'graph_sha256':c,'states':208,'rows':416,'dense_path':str(dense.relative_to(BASE)),'dense_sha256':h(dense)}
 dt=table(dense); order={q:i for i,q in enumerate(sorted({q for q,b in t}))};order[254]=208
 need(dt=={(order[q],b):(w,d,order[r]) for (q,b),(w,d,r) in t.items()})
 item['normalized_native_sha256']=hashlib.sha256(json.dumps(sorted((q,b,w,d,r) for (q,b),(w,d,r) in t.items()),separators=(',',':')).encode()).hexdigest()
 item['dense_conjugacy_rows']=416
 sp=p.with_name('u208.sites.json')
 if not sp.exists():sp=p.with_name('sites.json')
 if 'u208_compatibility' in p.name:sp=p.parent.parent/'comparison/compatibility/sites.json'
 if not sp.exists(): raise ValueError('source not found '+str(sp))
 item['source_path']=str(sp.relative_to(BASE));item['source_sha256']=h(sp)
 items.append(item);tables[key]=(t,n);classes[c].append(key)
witness=[]
for c,ks in classes.items():
 root=ks[0];rt,rn=tables[root]
 for k in ks[1:]:
  t,n=tables[k];inv={v:q for q,v in n.items()};mp={q:inv[v] for q,v in rn.items()}
  for (q,b),(w,d,r) in rt.items():need(t[mp[q],b]==(w,d,mp[r]))
  witness.append({'from':root,'to':k,'map':mp,'rows_verified':416,'nonidentity':{q:r for q,r in mp.items() if q!=r}})
r={'machines':items,'classes':dict(classes),'distinct_native':len(set(x['native_sha256'] for x in items)),'graph_classes':len(classes),'distinct_normalized_native':len(set(x['normalized_native_sha256'] for x in items)),'distinct_sources':len(set(x['source_sha256'] for x in items)),'witnesses':witness}
(BASE/'comparison/comparison.json').write_text(json.dumps(r,indent=2)+'\n')
print('Graphs',len(classes),'bytevariants',r['distinct_native'])
for c,ks in classes.items():print(c, '\n  '+'\n  '.join(ks))
print('Nonidentity witnesses:')
for w in witness:print(w['from'].split('/')[1],'=>',w['to'].split('/')[1],w['nonidentity'])
