#!/usr/bin/env python3
from search_support import *
start=time.time();count=0;success=[];fail=collections.Counter();edge_snap={};byedge=collections.defaultdict(set)
# Literal-row snapshots. sstep emits True exactly when it takes one physical
# transition; accelerated constant-symbol loops are excluded as predecessors.
for k,c in enumerate(cs):
 st=c[2];moved=False
 for step in range(2048):
  if moved and (st[0]==254 if c[3] is None else s.matches(st,c[3])):break
  nxt=s.sstep(rows,c[1],st)
  if nxt is None:raise ValueError((k,st))
  new,m=nxt
  if m:
   assert not st[1]
   bit=s.headbit(st[3]);assert bit in (0,1)
   key=(st[0],bit);byedge[key].add(k)
   edge_snap.setdefault((k,key),st)
  st=new;moved|=m
incoming=collections.defaultdict(list)
for key,act in rows.items():incoming[act[2]].append(key)
states=sorted(set(q for q,b in rows)-s.BOXSTATES-{84})
results=[]
for qi,q in enumerate(states):
 edges=incoming[q]
 if any(p in s.BOXSTATES for p,b in edges):continue
 options={};rr=dict(rows)
 for edge in edges:
  active=sorted(byedge[edge],key=lambda k:-fail[k]);loc=[(k,(cs[k][0],cs[k][1],edge_snap[k,edge],cs[k][3]))for k in active]
  choices=[];orig=rows[edge]
  acts=list(itertools.product((0,1),(False,True),set(x for x,b in rows)-{q}))
  acts.sort(key=lambda a:(a[:2]!=orig[:2],a))
  for act in acts:
   count+=1;rr[edge]=act
   def observe(st):
    if st[0]==q:raise RuntimeError('removed control reached')
   for k,c in loc:
    try:v=s.run(rr,c,fuel=1024,observe=observe)
    except RuntimeError:v=None
    if v is None:fail[k]+=1;break
   else:choices.append(act)
  rr[edge]=orig
  options[edge]=choices
  if not choices:break
 if len(options)==len(edges) and all(options.values()):
  tried=0;keys=list(options)
  for acts in itertools.product(*(options[k]for k in keys)):
   tr={key:act for key,act in rows.items() if key[0]!=q};tr.update(zip(keys,acts));tr={k:a for k,a in tr.items()if k[0]!=q}
   if any(a[2]==q for a in tr.values()):continue
   tried+=1;v=s.validate(tr,cs)
   if v['ok']:
    hit={'removed':q,'rewrites':[[list(k),list(a)]for k,a in zip(keys,acts)],'verification':v};success.append(hit);print('HIT',hit,flush=True)
   if tried>=256:break
  results.append({'removed':q,'option_counts':{str(k):len(v)for k,v in options.items()},'combinations_tried':tried})
 if qi%10==0:print('progress',qi,len(states),'actions',count,'seconds',round(time.time()-start,2),'hits',len(success),flush=True)
receipt={'candidate_actions':count,'seconds':time.time()-start,'hits':success,'live_option_sets':results,'scope':'Delete a non-box reader and separately rethread every incoming literal row to any existing action. Full instruction endpoints; removed control forbidden in preliminary continuations; final complete source check.'}
(P/'incoming_thread_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
