from pathlib import Path
from collections import defaultdict
import sys,json,subprocess,time,itertools,hashlib
sys.path.insert(0,str(Path(__file__).parent));import compile_eq as c
ROOT=Path(__file__).resolve().parent.parent;OUT=Path(__file__).parent/'output/permutations';OUT.mkdir(parents=True,exist_ok=True)
BASE=c.T.copy();groups0={q:list(ps)for q,ps in c.P.items()};original_node={}
def visit(n,p=''):
 if c.s.leaf(n):return
 original_node[p]=n;visit(n[0],p+'0');visit(n[1],p+'1')
visit(c.TREE)
protected={tuple(x)for x in json.loads((c.BASE/'research/experiments/receipts/engine_protected.json').read_text())['rows']}
protected|={(q,b)for q,b in BASE if q not in groups0};protected|={(302,0),(302,1)}
def rename(n,perm):
 if c.s.leaf(n):return (n[0],perm[n[1]])if n[0]in('CI','CD')else n
 return tuple(rename(x,perm)for x in n)
def minimize(T):
 Q=sorted({q for q,b in T});P={q:0 for q in Q};P[254]=-1
 while True:
  ids={};N={q:ids.setdefault(tuple((w,d,P[z])for w,d,z in(T[q,0],T[q,1])),len(ids))for q in Q};N[254]=-1
  if all(P[q]==P[z]for q in Q for z in Q if N[q]==N[z])and all(N[q]==N[z]for q in Q for z in Q if P[q]==P[z]):break
  P=N
 blocks=defaultdict(list)
 for q in Q:blocks[N[q]].append(q)
 reps={q:(84 if 84 in vs else 0 if 0 in vs else min(vs))for vs in blocks.values()for q in vs};reps[254]=254
 NT={(reps[q],b):(w,d,reps[z])for(q,b),(w,d,z)in T.items()}
 return NT,reps

def compile(perm,name):
 nodes={p:rename(n,perm)for p,n in original_node.items()};groups={q:list(v)for q,v in groups0.items()};where={p:q for q,ps in groups.items()for p in ps};cache={k:v for k,v in BASE.items()};fresh=303;d=OUT/name;d.mkdir(parents=True,exist_ok=True);events=[]
 def move(q):
  nonlocal fresh
  z=fresh;fresh+=1;groups[z]=groups.pop(q)
  for p in groups[z]:where[p]=z
  for b in(0,1):cache[z,b]=cache[q,b]
  events.append(['clone',q,z]);return z
 def split(q):
  nonlocal fresh
  ps=groups[q];parts=defaultdict(list)
  for p in ps:
   sig=tuple(('L',ch)if c.s.leaf(ch)else('I',where[p+str(b)])for b,ch in enumerate(nodes[p]));parts[sig].append(p)
  if len(parts)==1:
   for k in range(1,10):
    parts=defaultdict(list)
    for p in ps:parts[p[-k:]].append(p)
    if len(parts)>1:break
  if len(parts)==1:raise ValueError(('unsplittable',q,ps,nodes[ps[0]]))
  blocks=sorted(parts.values(),key=lambda xs:-len(xs));groups[q]=blocks[0]
  for block in blocks[1:]:
   z=fresh;fresh+=1;groups[z]=block
   for p in block:where[p]=z
   for b in(0,1):cache[z,b]=cache[q,b]
  events.append(['split',q,len(blocks)])
 for iteration in range(300):
  T=BASE.copy();T.update({(q,b):cache[q,b]for q in groups for b in(0,1)});queries=[];meta={};qid=0;restart=False;changes=0
  for q,ps in list(groups.items()):
   for bit in(0,1):
    leaves=[];targets=set()
    for p in ps:
     ch=nodes[p][bit]
     if c.s.leaf(ch):leaves.append((p+str(bit),*ch))
     else:targets.add(where[p+str(bit)])
    action=cache[q,bit]
    if targets:
     def advances(pc,want):
      tape={-1:1,**{i:int(v)for i,v in enumerate(pc)}};before=tape.copy();h=len(pc)-1;state=q
      for tick in range(100):
       if h==len(pc):return state==want and tape==before
       if h not in tape or(state,tape[h])not in T:return False
       w,dd,state=action if tick==0 else T[state,tape[h]];tape[h]=w;h+=dd
      return False
     if not all(advances(p+str(bit),where[p+str(bit)])for p in ps if not c.s.leaf(nodes[p][bit])):
      if len(targets)>1:split(q);restart=True;break
      action=(bit,1,next(iter(targets)))
    if(q,bit)in protected and action!=BASE[q,bit]:move(q);restart=True;break
    T[q,bit]=action
    if cache[q,bit]!=action:cache[q,bit]=action;changes+=1
    if leaves:
     force=int(bool(targets)or(q,bit)in protected);queries.append(f'{qid} {bit} {force} '+' '.join(map(str,action))+f' {len(leaves)}\n'+''.join(f'{pc} {op} {arg if arg is not None else -1}\n'for pc,op,arg in leaves));meta[qid]=(q,bit,bool(targets));qid+=1
   if restart:break
  if restart:continue
  (d/'working.tm').write_bytes(c.b.table_bytes(T));(d/'queries.in').write_text(''.join(queries))
  run=subprocess.run([str(OUT.parent/'leaf_synth'),str(d/'working.tm'),str(d/'queries.in'),str(d/'answers.out')],capture_output=True,text=True)
  if run.returncode:raise ValueError(('synth error',run.stderr))
  for line in(d/'answers.out').read_text().splitlines():
   i,ok,w,dd,z=map(int,line.split());q,bit,internal=meta[i]
   if not ok:
    if(q,bit)in protected and not internal:move(q)
    else:split(q)
    restart=True;break
   action=(w,dd,z)
   if cache[q,bit]!=action:cache[q,bit]=action;changes+=1
   T[q,bit]=action
  if restart:continue
  if changes:continue
  # Everything has been checked against the same stable table.
  reach={0};todo=[0]
  for q in todo:
   for bit in(0,1):
    z=T[q,bit][2]
    if z!=254 and z not in reach:reach.add(z);todo.append(z)
  T={k:v for k,v in T.items()if k[0]in reach};NT,reps=minimize(T)
  tree=rename(c.TREE,perm);c.b.decoder_map(T,tree)
  (d/'candidate.native.tm').write_bytes(c.b.table_bytes(T));(d/'candidate.minimized.tm').write_bytes(c.b.table_bytes(NT));(d/'sites.json').write_bytes(c.s.compact(c.s.sites(tree)))
  (d/'sites.in').write_text(''.join(f'{pc} {op} {a if a is not None else -1}\n'for pc,op,a in c.s.sites(tree)))
  return {'permutation':perm,'states':len(T)//2,'minimized_states':len(NT)//2,'iterations':iteration+1,'events':events,'table_sha256':hashlib.sha256(c.b.table_bytes(T)).hexdigest()}
 raise ValueError(('iteration limit',events))
if __name__=='__main__':
 options=[('identity',list(range(9)))]
 if len(sys.argv)>1 and sys.argv[1]!='identity':
  for a,b in[(0,4),*itertools.combinations([1,2,3,5,6,7,8],2)]:
   perm=list(range(9));perm[a],perm[b]=b,a;options.append((f'swap{a}{b}',perm))
 results=[]
 for name,perm in options:
  start=time.monotonic()
  try:r={'name':name,**compile(perm,name)}
  except Exception as e:r={'name':name,'permutation':perm,'error':repr(e)}
  r['seconds']=time.monotonic()-start;results.append(r);print(json.dumps(r),flush=True);(OUT/'summary.json').write_text(json.dumps(results,indent=2))
