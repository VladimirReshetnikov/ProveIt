#!/usr/bin/env python3
"""Research search; relative-path packaging adaptation, algorithm unchanged."""
from pathlib import Path
if not __debug__:
    raise SystemExit("Assertions are required; do not use -O or PYTHONOPTIMIZE.")
exec(Path(__file__).with_name('new_helper_search.py').read_text().split('count=0;t0=time.time()')[0])
# Every helper pair that could supply one missing read action is eligible.
allhelpers=set();requirements={};base_edges=set((a,b) for a,b,_ in baseops)
for a,b in itertools.product(L,R):
 opt=[]
 for x in (0,1):
  if rows[a,x]==rows[b,x]:opt.append(None);continue
  if [v for v in providers[x].get((rows[a,x],rows[b,x]),[]) if not {a,b}&set(v)]:opt.append(None);continue
  uv={(u,v) for u in rev[x][rows[a,x]] for v in rev[x][rows[b,x]] if not {a,b}&{u,v}}
  opt.append(uv);allhelpers |= uv
 requirements[a,b]=opt
allhelpers=sorted(allhelpers); print('ALL_HELPERS',len(allhelpers),'potential_edges',sum(all(z is None or z for z in v)for v in requirements.values()),flush=True)
count=0;t0=time.time();maxbound=0;hits=[]
for i,h1 in enumerate(allhelpers):
 for h2 in allhelpers[i+1:]:
  capable=[]
  for (a,b),opts in requirements.items():
   if all(uv is None or h1 in uv or h2 in uv for uv in opts):capable.append((a,b,None))
  bound=len(c.max_matching(capable))
  if bound>maxbound:print('BEST_BOUND',bound,h1,h2,flush=True);maxbound=bound
  if bound<10:continue
  count+=1
  table=dict(rows)
  for h,(u,v) in zip((2400,2401),(h1,h2)):
   table[h,0]=(0,True,u);table[h,1]=(1,True,v)
  ops=c.opportunities_fast(table,shape)
  print('BOUND_PASS',h1,h2,bound,len(ops),flush=True)
  sol,n=solve(ops,table,10)
  if sol:
   rec={'helpers':[[2400,h1],[2401,h2]],'folds':sol,'raw_controls':len(qs),'final_controls':len(qs)+2-len(sol)}
   (OUTPUT_DIR/'twohelpers_hit.json').write_text(json.dumps(rec,indent=2));print('HIT',json.dumps(rec),flush=True);hits.append(rec);break
 if hits:break
print('DONE pairs',len(allhelpers)*(len(allhelpers)-1)//2,'bound_passes',count,'maxbound',maxbound,'elapsed',time.time()-t0,flush=True)
