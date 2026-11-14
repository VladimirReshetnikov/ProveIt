#!/usr/bin/env python3
import json,csv,itertools,time
from pathlib import Path
from collections import defaultdict
ROOT=Path('/home/agent/proveit_research_repo');OUT=Path(__file__).resolve().parent/'raw_helpers';OUT.mkdir(exist_ok=True)
def read(p):
 rows={};start=0
 for line in p.read_text().splitlines():
  if line.startswith('#! start'):start=int(line.split()[-1])
  line=line.split('#',1)[0].strip()
  if not line:continue
  q,b,w,d,n=line.split();rows[int(q),int(b)]=(int(w),d=='R',int(n))
 return rows,start

def matching(ops):
 adj=defaultdict(list)
 for a,b,_ in ops:adj[a].append(b)
 m={}
 def aug(a,seen):
  for b in adj[a]:
   if b in seen:continue
   seen.add(b)
   if b not in m or aug(m[b],seen):m[b]=a;return True
  return False
 for a in adj:aug(a,set())
 return len(m)
def valid(chosen,table):
 aliases={a:b for a,b,acts in chosen};patched={b:acts for a,b,acts in chosen}
 for a,b,ac in chosen:
  for ctx,old in ((0,a),(1,b)):
   for bit in (0,1):
    w,d,t=table[old,bit];target=(aliases.get(t,t),1 if d else -1,(ctx,w))
    q,h,tape=b,0,[ctx,bit]
    for step in range(21):
     if step and(q,h,tuple(tape))==target:break
     if h not in(-1,0)or(q,tape[h+1])not in table or q in aliases:return False
     w,d,t=patched[q][tape[h+1]]if q in patched else table[q,tape[h+1]]
     tape[h+1]=w;h+=1 if d else -1;q=aliases.get(t,t)
    else:return False
 return True

def solve(ops,table,goal):
 chosen=[];used=set();trials=0
 def dfs(i):
  nonlocal trials
  if len(chosen)==goal:
   trials+=1
   if valid(chosen,table):return list(chosen)
   return
  if i==len(ops)or len(chosen)+len(ops)-i<goal:return
  a,b,acts=ops[i]
  if not{a,b}&used:
   used.update((a,b))
   for ac in itertools.product(*acts):
    chosen.append((a,b,ac));r=dfs(i+1)
    if r:return r
    chosen.pop()
   used.remove(a);used.remove(b)
  return dfs(i+1)
 return dfs(0),trials

def run(rows,start):
 qs=sorted({q for q,b in rows});inc={q:set()for q in qs};bad=set()
 for (q,bit),(w,d,n)in rows.items():
  if n not in inc:continue
  if d:inc[n].add(w)
  else:bad.add(n)
 L=[q for q in qs if inc[q]=={0}and q not in bad and q!=start]
 R=[q for q in qs if inc[q]=={1}and q not in bad and q!=start]
 providers=[defaultdict(list),defaultdict(list)];rev=[defaultdict(set),defaultdict(set)]
 for q in qs:
  for b in(0,1):rev[b][rows[q,b]].add(q)
  z,o=rows[q,0],rows[q,1]
  if z[:2]==(0,True)and o[:2]==(1,True)and z[2]in qs and o[2]in qs:
   for b in(0,1):providers[b][rows[z[2],b],rows[o[2],b]].append((q,z[2],o[2]))
 pairs=[];helpers=set();oldops=[]
 for a,b in itertools.product(L,R):
  opts=[];missing=[]
  for x in(0,1):
   if rows[a,x]==rows[b,x]:opts.append([rows[a,x]]);continue
   pp=[v for v in providers[x].get((rows[a,x],rows[b,x]),[])if not{a,b}&set(v)]
   opts.append([(x,False,h)for h,u,v in pp])
   if not pp:missing.append({(u,v)for u in rev[x][rows[a,x]]for v in rev[x][rows[b,x]]if not{a,b}&{u,v}})
  if all(opts):oldops.append((a,b,opts))
  if missing:helpers|=set.intersection(*missing)
  pairs.append((a,b,opts))
 H=max(qs+[n for w,d,n in rows.values()])+1
 goal=len(qs)-192;basebound=matching(oldops);bestbound=basebound;screened=0;hits=[];trials=0
 for u,v in sorted(helpers):
  ops=[]
  for a,b,options in pairs:
   opt=[list(x)for x in options]
   if not{a,b}&{u,v}:
    for x in(0,1):
     if rows[a,x]!=rows[b,x]and rows[u,x]==rows[a,x]and rows[v,x]==rows[b,x]:opt[x].append((x,False,H))
   if all(opt):ops.append((a,b,opt))
  bound=matching(ops);bestbound=max(bestbound,bound)
  if bound<goal:continue
  screened+=1;table=dict(rows);table[H,0]=(0,True,u);table[H,1]=(1,True,v)
  result,n=solve(ops,table,goal);trials+=n
  if result:hits.append(dict(helper=[H,u,v],folds=result,states=len(qs)+1-len(result)));break
 return dict(controls=len(qs),left=len(L),right=len(R),base_matching=basebound,helpers=len(helpers),best_matching=bestbound,goal=goal,bound_passes=screened,trials=trials,hits=hits)
items=[];t0=time.time()
for rec in csv.DictReader((ROOT/'Computability/BusyBeaver/Research/PA/docs/MACHINES.tsv').open(),delimiter='\t'):
 if int(rec['states'])not in(195,196,197,198,199,200,201,202):continue
 if '/comparison/'in rec['kept_file']or'/census/'in rec['kept_file']:continue
 p=ROOT/rec['kept_file'];rows,start=read(p)
 result=run(rows,start);result.update(path=rec['kept_file'],table_class=rec['table_class']);items.append(result)
 print(len(items),len(rows)//2,rec['first_packet'],'base',result['base_matching'],'best',result['best_matching'],'target',result['goal'],'hits',len(result['hits']),flush=True)
 if result['hits']:(OUT/f'hit_{rec["class"][:12]}.json').write_text(json.dumps(result,indent=2)+'\n')
(OUT/'results.json').write_text(json.dumps(items,indent=2)+'\n');print('DONE',len(items),time.time()-t0,'seconds',sum(len(x['hits'])for x in items),'hits')
