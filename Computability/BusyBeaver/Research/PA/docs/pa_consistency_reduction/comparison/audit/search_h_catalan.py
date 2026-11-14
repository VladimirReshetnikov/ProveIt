#!/usr/bin/env python3
from pathlib import Path
import sys,json,time,itertools,collections
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'verification'));import symbolic as S
out=Path(__file__).parent;start=time.monotonic();machine=S.load_machine();tree,nodes=S.source_tree();maps=json.loads((Path(__file__).resolve().parents[2]/'verification/node_map.json').read_text())
seed=[(tuple(p),tuple(op)) for p,op in json.loads((out/'h_only_seed_sites.json').read_text())];desired=S.instructions(seed)
def shapes(v):
 if len(v)==1:return [v[0]]
 return [(a,b) for i in range(1,len(v)) for a in shapes(v[:i]) for b in shapes(v[i:])]
def expand(t,atoms):return atoms[t] if isinstance(t,int) else (expand(t[0],atoms),expand(t[1],atoms))
def replace(t,a,b):
 if t==a:return b
 if t[0]=='leaf':return t
 return replace(t[0],a,b),replace(t[1],a,b)
def repair_jumps(sites):
 # Preserve exact opcode indices, registers and ordinal control graph.
 fixed=[];changes=[]
 prefixes={}
 for i,(p,op) in enumerate(sites):
  for k in range(len(p)+1):prefixes.setdefault(p[:k],i)
 def locate(p):
  if p is None:return 0
  if p in prefixes:return prefixes[p]
  for k in range(len(p)-1,-1,-1):
   if p[k:] and any(p[k:]):break
   if p[:k] in prefixes:return prefixes[p[:k]]
  raise ValueError(p)
 for i,(p,op) in enumerate(sites):
  if op[0] not in ('continueTo','breakTo'):fixed.append((p,op));continue
  found=[]
  for tag in ('continueTo','breakTo'):
   for k in range(0,1+len(p)):
    try:dst=locate(S.cut(p,1,k) if tag=='continueTo' else S.successor(S.cut(p,0,k)))
    except ValueError:continue
    if dst==desired[i][1]:found.append((tag,k))
  if op in found:new=op
  elif found:new=found[0]
  else:return None,None
  fixed.append((p,new))
  if new!=op:changes.append((i,op,new))
 try:
  if S.instructions(fixed)!=desired:return None,None
 except ValueError:return None,None
 return fixed,changes
records=[];hits=[]
for root,atomnames,innernames in [('node170',['node36','node167','node145','node57'],['node170','node169','node168']),('node171',['node36','node167','node145','node57','node23'],['node171','node170','node169','node168'])]:
 atoms=[nodes[n] for n in atomnames];entries=[maps[n][0] for n in atomnames];qs=[maps[n][0] for n in innernames]
 for si,shape in enumerate(shapes(list(range(len(atoms))))):
  sites=S.flatten(replace(tree,nodes[root],expand(shape,atoms)))
  fixed,changes=repair_jumps(sites)
  if fixed is None:records.append({'root':root,'shape':shape,'skip':'no identical CFG via jump depths'});continue
  for perm in itertools.permutations(qs[1:]):
   states=iter([qs[0]]+list(perm));m=dict(machine)
   def compile(t):
    if isinstance(t,int):return entries[t]
    q=next(states);a=compile(t[0]);b=compile(t[1]);m[q,0]=(0,1,a);m[q,1]=(1,1,b);return q
   compile(shape);S.all_sites=lambda:fixed
   bad=[];passed=0
   for i,b,br,s,t in S.contracts():
    if S.execute(m,br,s,t) is None:bad.append((i,b))
    else:passed+=1
   item={'root':root,'shape':shape,'perm':perm,'jump_changes':changes,'passed':passed,'failed':bad};records.append(item)
   print(root,si,perm,'pass',passed,'bad',bad[:20],'jumps',changes,flush=True)
   if not bad:
    stem=f'h_catalan_{root}_{si}_'+('_'.join(map(str,perm)));item['stem']=stem;hits.append(item)
    (out/(stem+'.tm')).write_text(''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n' for(q,b),(w,d,z)in sorted(m.items())))
    (out/(stem+'_sites.json')).write_text(json.dumps(fixed)+'\n')
report={'records':records,'hits':hits,'seconds':time.monotonic()-start};(out/'h_catalan_results.json').write_text(json.dumps(report,indent=2)+'\n');print('DONE',len(records),'hits',len(hits),'seconds',time.monotonic()-start,flush=True)
