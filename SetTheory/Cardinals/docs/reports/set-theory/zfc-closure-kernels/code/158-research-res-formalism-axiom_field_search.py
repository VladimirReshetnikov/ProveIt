#!/usr/bin/env python3
"""Calibrated independent renaming of input fields in complete axiom schemas."""
from pathlib import Path
import os
import sys,json,itertools,time,random,heapq
HERE=Path(__file__).resolve().parent;Z=Path(os.environ.get('PROVEIT_ZFC_ROOT', str(HERE.parent/'ProveIt/Computability/BusyBeaver/Research/ZFC'))).resolve();sys.path.insert(0,str(Z/'k218-quantifier-stability/pricing'))
import source_language as s,build221 as b
root=s.tree(json.loads((Z/'candidate-k218/sites218.json').read_text()));tab=b.read_table((Z/'candidate-k218/k218.native.tm').read_bytes());g,_=b.decoder_map(tab,root);q=lambda k:b.sole(g,k)
macros=[q(98),q(12),q(166)];rev={t:i for i,t in enumerate(macros)}
ranges=[('rho8',135,486),('G',486,895),('rho6',895,1178),('rho5',1178,1474),('rho4',1474,1773),('rho3',1773,2069),('rho2',2069,2419),('rho1',2419,2650),('bundle',2650,4563)]
perms=list(itertools.permutations(range(3)));assert perms[0]==(0,1,2);allowed=[list(range(6))for _ in ranges];allowed[-1]=[0,2] # swap a,b only: perms2=(1,0,2)
assert perms[2]==(1,0,2)
nodes=[];index={}
def intern(t):
 if t in index:return index[t]
 i=len(nodes);index[t]=i;nodes.append(t);return i
def atom(t):
 return intern(t)if s.leaf(t)else intern((atom(t[0]),atom(t[1])))
base=atom(root);macroIds=list(map(atom,macros));B=len(nodes)
tpl=[];ti={}
def tin(t):
 if t in ti:return ti[t]
 i=len(tpl);ti[t]=i;tpl.append(t);return i
counts=[0]*len(ranges)
def make(t,lo=0):
 hi=lo+len(s.sites(t))
 if t in rev:
  for k,(_,a,bb)in enumerate(ranges):
   if a<=lo and hi<=bb:counts[k]+=1;return tin(('var',k,rev[t]))
 if s.leaf(t):return tin(('const',atom(t)))
 return tin(('pair',make(t[0],lo),make(t[1],lo+len(s.sites(t[0])))))
tr=make(root);print('RANGES',list(zip(ranges,counts)),flush=True)
def realize(tid,assign,cache):
 if tid in cache:return cache[tid]
 t=tpl[tid]
 if t[0]=='const':ans=t[1]
 elif t[0]=='var':ans=macroIds[perms[assign[t[1]]][t[2]]]
 else:ans=intern((realize(t[1],assign,cache),realize(t[2],assign,cache)))
 cache[tid]=ans;return ans
def size(n):
 seen=set();todo=[n]
 while todo:
  k=todo.pop()
  if k in seen:continue
  seen.add(k);t=nodes[k]
  if isinstance(t[0],int):todo.extend(t)
 return len(seen)
def decode(n):
 t=nodes[n];return t if not isinstance(t[0],int)else(decode(t[0]),decode(t[1]))
def evaluate(a):
 n=realize(tr,a,{});return size(n),n
initial=(0,)*len(ranges);assert evaluate(initial)==(205,base)
out=HERE/'axiom-field-search';out.mkdir(exist_ok=True);rng=random.Random(2501);visited={};beam=[(205,initial,base)];best=205;start=time.monotonic();trials=0;generation=0
while time.monotonic()-start<110 and len(nodes)<1400000:
 pool={a:(sc,n)for sc,a,n in beam}
 for _,a,_ in beam:
  for k in range(len(ranges)):
   for v in allowed[k]:
    if v==a[k]:continue
    aa=a[:k]+(v,)+a[k+1:]
    if aa in visited:continue
    sc,n=evaluate(aa);visited[aa]=sc;trials+=1
    if sc<=best:
     pool[aa]=(sc,n)
     if sc<best:
      best=sc;t=decode(n);rr=s.sites(t);assert s.metrics(t)['dag_nodes']==sc;assert s.graph_intervals(rr)==s.graph_arithmetic(rr)[0]
      d=out/f'candidate{trials:07d}';d.mkdir(exist_ok=True);(d/'sites.json').write_bytes(s.compact(rr));info=dict(assignments=aa,permutations=[perms[x]for x in aa],ranges=ranges,metrics=s.metrics(t),trials=trials,seconds=time.monotonic()-start);(d/'result.json').write_text(json.dumps(info,indent=2));print('BEST',info,flush=True)
  if time.monotonic()-start>=110 or len(nodes)>=1400000:break
 keys=list(pool);rng.shuffle(keys);keys.sort(key=lambda a:pool[a][0]);beam=[(pool[a][0],a,pool[a][1])for a in keys[:200]];generation+=1
 print('ROUND',generation,'best',best,'trials',trials,'nodes',len(nodes),'beam',len(beam),'time',round(time.monotonic()-start,3),flush=True)
 if generation>1 and all(all(a[:k]+(v,)+a[k+1:]in visited for v in allowed[k]if v!=a[k])for _,a,_ in beam for k in range(len(ranges))):
  # Add random simultaneous field reassignments near the best plateau.
  for _ in range(150):
   _,a,_=rng.choice(beam);ks=rng.sample(range(len(ranges)),3);aa=list(a)
   for k in ks:aa[k]=rng.choice(allowed[k])
   aa=tuple(aa)
   if aa not in visited:
    sc,n=evaluate(aa);visited[aa]=sc;trials+=1
    if sc<=best+2:beam.append((sc,aa,n))
  rng.shuffle(beam);beam.sort(key=lambda x:x[0]);beam=beam[:250]
result=dict(trials=trials,best=best,seconds=time.monotonic()-start,nodes=len(nodes),beam=[dict(cost=sc,assign=a)for sc,a,n in beam[:20]],scope='Source grammar census, complete axiom-schema input renamings; no allocator/runtime/startup.')
(out/'result.json').write_text(json.dumps(result,indent=2));print('DONE',result,flush=True)
