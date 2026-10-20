#!/usr/bin/env python3
"""Cyclically rebase the four closed top-level enumerator phases."""
from pathlib import Path
import hashlib,json,subprocess,sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'source_work'));import rotation_search as r
OUT=ROOT/'source218/cyclic_phase_chain';OUT.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def rebuild(xs):
 return xs[0]if len(xs)==1 else(xs[0],rebuild(xs[1:]))
def checkprefix(oldT,old,newT,new,merged):
 groups,paths,node_states=r.mapping(oldT,old)
 # Prefix states of the three outer sequence nodes are assigned in order.
 outer=['','1','11'];assigned={}
 q=84
 for p in outer:
  assigned[r.s.subtree(new,p)]={q}
  q=oldT[q,1][2]
 allowed={n:set(qs)for n,qs in node_states.items()};allowed.update(assigned)
 if merged:allowed={n:{88 if q==301 else q for q in qs}for n,qs in allowed.items()}
 failures=[]
 def visit(n,p=''):
  if r.s.leaf(n):return
  tape={-1:1,**{i:int(v)for i,v in enumerate(p)}};before=dict(tape);head=0;q=84
  for tick in range(10000):
   if head==len(p):break
   if head not in tape or(q,tape[head])not in newT:break
   w,d,q=newT[q,tape[head]];tape[head]=w;head+=d
  if head!=len(p)or tape!=before or q not in allowed.get(n,()):
   failures.append({'path':p,'state':q,'allowed':sorted(allowed.get(n,())),'head':head,'tape_changed':tape!=before})
  visit(n[0],p+'0');visit(n[1],p+'1')
 visit(new);return failures
results=[]
for label,tablepath,sourcepath in [
 ('published',ROOT/'baseline219/K219_Construction_2026-10-20/machine/k219.native.tm',ROOT/'baseline219/K219_Construction_2026-10-20/machine/sites219.json'),
 ('alternative',ROOT/'source218/alternative219/candidate.tm',ROOT/'source218/alternative219/sites.json')]:
 T=r.b.read_table(tablepath.read_bytes());oldrows=json.loads(sourcepath.read_text());old=r.s.tree(oldrows)
 phases=[r.s.subtree(old,p)for p in('0','10','110','111')]
 assert rebuild(phases)==old and all(r.s.boundary(x)[:2]==(0,0)for x in phases)
 phaseq=[];outerq=[];q=84
 for i in range(3):
  outerq.append(q);a,b=T[q,0],T[q,1]
  assert a[:2]==(0,1)and b[:2]==(1,1)
  phaseq.append(a[2]);q=b[2]
 phaseq.append(q)
 og=r.s.graph_arithmetic(oldrows)[0];assert og==r.s.graph_intervals(oldrows)
 for k in(1,2,3):
  cut=sum(len(r.s.sites(p))for p in phases[:k]);order=list(range(k,4))+list(range(k))
  new=rebuild([phases[i]for i in order]);rows=r.s.sites(new);ng=r.s.graph_arithmetic(rows)[0]
  assert ng==r.s.graph_intervals(rows)
  assert [x[1:]for x in rows]==[x[1:]for x in oldrows[cut:]+oldrows[:cut]]
  expected=[[og[i][0],[(j-cut)%len(rows)for j in og[i][1]]]for i in list(range(cut,len(rows)))+list(range(cut))]
  assert ng==expected
  U=dict(T)
  for i,q in enumerate(outerq):
   U[q,0]=(0,1,phaseq[order[i]])
   U[q,1]=(1,1,outerq[i+1]if i<2 else phaseq[order[3]])
  folder=OUT/f'{label}_{k}';folder.mkdir(exist_ok=True)
  (folder/'sites.json').write_bytes(r.s.compact(rows))
  for count in(219,218):
   V=dict(U)
   if count==218:
    V={(q,b):(w,d,88 if z==301 else z)for(q,b),(w,d,z)in V.items()if q!=301}
    V[88,0]=(0,-1,51);V[88,1]=(1,1,103);V[51,0]=(0,1,122);V[51,1]=(1,1,51)
   (folder/f'phase{count}.tm').write_bytes(r.b.table_bytes(V))
   fails=checkprefix(T,old,V,new,count==218)
   with(folder/f'start{count}.txt').open('w')as of,(folder/f'start{count}.log').open('w')as ef:
    subprocess.run([str(ROOT/'source218/alternative301_search/search_start_weak'),str(folder/f'phase{count}.tm'),'3000000'],stdout=of,stderr=ef,check=True)
   lines=(folder/f'start{count}.txt').read_text().splitlines()
   rec={'layout':label,'rotation':k,'state_count':count,'old_ordinal_cut':cut,'source_metrics':r.s.metrics(new),
        'source_sha256':sha(folder/'sites.json'),'table_sha256':sha(folder/f'phase{count}.tm'),
        'exact_cyclic_cfg_conjugacy':True,'prefix_failures':fails,
        'startup_hits':len(lines),'startup_output':lines,'folder':str(folder.relative_to(ROOT))}
   results.append(rec);(folder/f'receipt{count}.json').write_text(json.dumps(rec,indent=2)+'\n')
   print(json.dumps({k:v for k,v in rec.items()if k not in('prefix_failures','startup_output')}),flush=True)
(OUT/'summary.json').write_text(json.dumps({'status':'COMPLETED','results':results},indent=2)+'\n')
