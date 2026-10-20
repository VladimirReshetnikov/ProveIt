import sys
sys.path.insert(0,'research_sub224/source_search')
#!/usr/bin/env python3
"""Experimental source-aware allocator on exact224. Finite discovery only.
Every artifact requires independent complete source, startup, and runtime proof.
"""
from search_rotations import *
from functools import cache
import os
sys.path.insert(0,'research_sub224/intake/extracted/K224_Construction_2026-10-20/portable/machine/vendor');import independent_runtime as rt
B=Path('research_sub224/intake/extracted/K224_Construction_2026-10-20/portable/machine');T,START=v.table(Path('research_sub222/delivery/K221_Construction_2026-10-20/machine/k221.native.tm'));tr=Trees();base=tr.read(json.loads(Path('research_sub222/delivery/K221_Construction_2026-10-20/machine/sites221.json').read_text()));M=mapping(T,base,tr,84);NQ={n:q for q,ns in M.items()for n in ns};SOURCEQS=set(M)
MP={int(q):z for q,z in json.loads((B/'reference/legacy_state_map.json').read_text())['k230_to_old'].items()};MP[254]=254
J=json.loads(Path('research_sub224/source_search/interfaces.json').read_text());assert J.get('complete');F=set(map(tuple,J['source_helper_rows']));HELPQS={q for q,b in F}
CAT=collections.defaultdict(list)
for n,q in NQ.items():
 for b,c in enumerate(tr.nodes[n]):
  if tr.leaf(c)and T[q,b]not in CAT[tr.nodes[c],b]:CAT[tr.nodes[c],b].append(T[q,b])

def compile(path,out):
 nr=tr.read(json.loads(Path(path).read_text()));paths=collections.defaultdict(list)
 def visit(n,p=''):
  if tr.leaf(n):return
  paths[n].append(p)
  for b,c in enumerate(tr.nodes[n]):visit(c,p+str(b))
 visit(nr);live=set(paths);alloc={n:NQ[n]for n in live if n in NQ};same=set(alloc);alloc[nr]=84;NT=T.copy();available=sorted(SOURCEQS-set(alloc.values())-HELPQS);priority=[int(x)for x in os.environ.get('HELPER_ORDER','').split(',')if x];unusedhelp=sorted(HELPQS-set(alloc.values()),key=lambda q:(priority.index(q)if q in priority else len(priority),q));fresh=[];reuse=[];oldpathq={}
 def opath(n,p=''):
  if tr.leaf(n):return
  oldpathq[p]=NQ[n]
  for b,c in enumerate(tr.nodes[n]):opath(c,p+str(b))
 opath(base)
 def macro_ok(q,b,action,target,pp):
  for p in pp:
   mem={i-len(p):int(x)for i,x in enumerate(p)};mem[-len(p)-1]=1;mem[0]=b;orig=mem.copy();h=0;state=q
   for step in range(65):
    if h not in mem or(state,mem[h])not in NT:return False
    w,d,state=action if step==0 else NT[state,mem[h]];mem[h]=w;h+=d
    if h==1:
     if state!=target or mem!=orig:return False
     break
   else:return False
  return True
 @cache
 def primitive_ok(action,pc,op,arg):
  for pos in((False,True)if op=='CD'else(False,)):
   regs=[0]*9
   if pos:regs[arg]=1
   ones=rt.frame(pc,regs,[0]);q=-1;h=len(pc)-1
   for step in range(20000):
    if step and(q==254 or rt.clean_dispatch(96 if q==84 else -1,h,ones)):break
    if step and(q,int(h in ones))not in T:return False
    b=int(h in ones);w,d,q=action if step==0 else T[q,b]
    if w:ones.add(h)
    else:ones.discard(h)
    h+=d
   else:return False
   want=rt.expected((pc,op,arg),regs,[0]);actual=(96 if q==84 else q,h,ones)
   if not(actual[0]==254 if want is None else actual==want[0]):return False
  return True
 def options(n,b,c):
  if not tr.leaf(c):return [(b,1,alloc[c])]
  op,arg=tr.nodes[c]
  if op=='CH':return [(b,1,254)]
  acts=list(CAT[tr.nodes[c],b])
  # A canonical right-moving arithmetic entry can cross from either edge.
  for ob in(0,1):
   for w,d,z in CAT[tr.nodes[c],ob]:
    if(w,d)==(ob,1)and(b,1,z)not in acts:acts.append((b,1,z))
  acts.sort(key=lambda a:(a[:2]!=(b,1),a))
  return acts if os.environ.get('SKIP_PRIMITIVE_SCREEN') and op not in ('CB','CC') else [a for a in acts if all(primitive_ok(a,p+str(b),op,arg)for p in paths[n])]
 def eligible(q,n):
  actions=[]
  for b,c in enumerate(tr.nodes[n]):
   opts=options(n,b,c)
   if not opts:return None
   if(q,b)in F:
    if T[q,b]in opts:want=T[q,b]
    elif not tr.leaf(c)and macro_ok(q,b,T[q,b],alloc[c],paths[n]):want=T[q,b]
    else:return None
   else:want=opts[0]
   actions.append(want)
  return actions
 seen=set()
 def allocate(n):
  if tr.leaf(n)or n in seen:return
  seen.add(n)
  for c in tr.nodes[n]:allocate(c)
  if n in same:
   q=alloc[n]
   for b,c in enumerate(tr.nodes[n]):
    if not tr.leaf(c) and not macro_ok(q,b,NT[q,b],alloc[c],paths[n]) and (q,b) not in F:NT[q,b]=(b,1,alloc[c])
   return
  if n==nr:
   q=84;actions=eligible(q,n)
   if actions is None:raise ValueError(('root_allocation',n))
  else:
   for q in unusedhelp:
    actions=eligible(q,n)
    if actions is not None:unusedhelp.remove(q);alloc[n]=q;reuse.append((n,q));break
   else:
    oldqs=[oldpathq[p]for p in paths[n]if p in oldpathq and oldpathq[p]in available];q=oldqs[0]if oldqs else available[0]if available else max({q for q,b in NT}|set(alloc.values()))+1
    if q==254:q+=1
    if q in available:available.remove(q)
    alloc[n]=q;fresh.append((n,q));actions=eligible(q,n)
    if actions is None:raise ValueError(('new_node_primitive',n,q,[tr.nodes[c]for c in tr.nodes[n]]))
  for b,act in enumerate(actions):NT[q,b]=act
 try:
  allocate(nr)
  for q in available:NT.pop((q,0));NT.pop((q,1))
  if any(NT.get(x)!=T[x]for x in F):raise ValueError('frozen helper changed')
  badref={z for w,d,z in NT.values()}-{q for q,b in NT}-{254}
  if badref:raise ValueError(('undefined_targets',badref))
  failures=[]
  for n,q in alloc.items():
   for b,c in enumerate(tr.nodes[n]):
    if not tr.leaf(c)and not macro_ok(q,b,NT[q,b],alloc[c],paths[n]):failures.append((q,b,n,alloc[c]))
  # Keep source/primitives intact even when a different allocation has dead rows;
  # reachability pruning is separate and recorded.
  reach={0};todo=[0]
  while todo:
   q=todo.pop()
   for b in(0,1):
    z=NT[q,b][2]
    if z!=254 and z not in reach:reach.add(z);todo.append(z)
  pruned=sorted({q for q,b in NT}-reach);NT={k:v for k,v in NT.items()if k[0]in reach}
  out=Path(out);out.mkdir(parents=True,exist_ok=True);(out/'candidate.tm').write_bytes(encode(NT,0));(out/'sites.json').write_text(json.dumps(tr.sites(nr),separators=(',',':'))+'\n');(out/'allocation.json').write_text(json.dumps(dict(allocation=alloc,structures=tr.nodes,root=nr),indent=2)+'\n')
  res=dict(status='UNVERIFIED_CURRENT224_SOURCE_ALLOCATION',input=str(path),states=len(NT)//2,source_metrics=tr.metrics(nr),decision_nodes=len(alloc),reused_idle_helpers=reuse,unused_helpers=unusedhelp,fresh=fresh,pruned=pruned,decoder_ok=not failures,decoder_failures=failures,complete_runtime_proof=False,complete_startup_proof=False)
 except Exception as e:res=dict(status='COMPILE_FAILED',input=str(path),error=repr(e))
 Path(out).mkdir(parents=True,exist_ok=True);(Path(out)/'compile.json').write_text(json.dumps(res,indent=2)+'\n');return res
if __name__=='__main__':
 print(json.dumps(compile(sys.argv[1],sys.argv[2]),indent=2),flush=True)
