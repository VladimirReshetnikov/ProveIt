#!/usr/bin/env python3
"""Search exact CFG-preserving source rotations that delete a decoder state."""
import sys,json,time
from pathlib import Path
from collections import defaultdict,deque
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'verification'))
import symbolic as S
out=Path(__file__).parent;start=time.monotonic();m=S.load_machine();tree,nodes=S.source_tree();oldsites=S.flatten(tree);oldcfg=S.instructions(oldsites)
leaf=lambda t:t[0]=='leaf'
state_for=defaultdict(set);tree_for=defaultdict(set);todo=deque();seen=set()
def add(t,q):
 if (t,q) not in seen:seen.add((t,q));state_for[t].add(q);tree_for[q].add(t);todo.append((t,q))
add(tree,S.ROOT)
exact=json.loads((Path(__file__).resolve().parents[2]/'verification/node_map.json').read_text())
for k,qs in exact.items():
 for q in qs:add(nodes[k],q)
for k,t in nodes.items():
 if k.startswith('x') and k[1:].isdigit() and 1300+int(k[1:]) in S.LITERAL:add(t,S.LITERAL[1300+int(k[1:])])
while todo:
 t,q=todo.popleft()
 if not leaf(t) and all(m.get((q,b),(None,None,None))[:2]==(b,1) for b in (0,1)):
  for b in (0,1):add(t[b],m[q,b][2])
print('mapped',len(state_for),'trees',len(tree_for),'states',flush=True)
incoming=defaultdict(list)
for k,(w,d,z) in m.items():incoming[z].append(k)
rejected=[];hits=[];candidates=[]
def replace(t,a,b):
 if t==a:return b
 if leaf(t):return t
 return (replace(t[0],a,b),replace(t[1],a,b))
for k,t in nodes.items():
 if not k.startswith('x') or not k[1:].isdigit():continue
 for q in state_for[t]:
  if tree_for[q]!={t}:continue
  if not all(m[q,b][:2]==(b,1) for b in(0,1)):continue
  for direction in ('L','R'):
   if direction=='L':
    if leaf(t[0]):continue
    a,b=t[0];c=t[1];u=m[q,0][2];want=(b,c);v0=state_for[a];v1=state_for[want];nt=(a,want);edge=(q,0)
   else:
    if leaf(t[1]):continue
    a=t[0];b,c=t[1];u=m[q,1][2];want=(a,b);v0=state_for[want];v1=state_for[c];nt=(want,c);edge=(q,1)
   if not v0 or not v1:continue
   item={'node':k,'q':q,'native_q':S.LABELS[q],'u':u,'native_u':S.LABELS[u],'direction':direction,'incoming_inner':incoming[u],'v0':list(v0),'v1':list(v1)}
   if incoming[u]!=[edge]:item['reason']='inner not exclusively incoming';rejected.append(item);continue
   newtree=replace(tree,t,nt);newsites=S.flatten(newtree)
   if S.instructions(newsites)!=oldcfg:item['reason']='CFG changes';rejected.append(item);continue
   if newsites[25][0]!=oldsites[25][0]:item['reason']='startup path changes';rejected.append(item);continue
   for x in v0:
    for y in v1:
     if u in (x,y):continue
     nm={key:value for key,value in m.items() if key[0]!=u};nm[q,0]=(0,1,x);nm[q,1]=(1,1,y)
     if not S.check_engine(nm):continue
     S.all_sites=lambda:S.flatten(newtree)
     result={**item,'targets':[x,y]}
     try:
      summary,_=S.verify(nm);result['summary']=summary;hits.append(result)
      name=f'rotation_{k}_{direction}_{x}_{y}'
      (out/(name+'.tm')).write_text(''.join(f'{v} {b} {w} {"R" if d==1 else "L"} {z}\n' for (v,b),(w,d,z) in sorted(nm.items())))
      (out/(name+'_sites.json')).write_text(json.dumps(newsites)+'\n')
      print('HIT',result,flush=True)
     except AssertionError as exc:result['failure']=str(exc)
     candidates.append(result)
S.all_sites=lambda:oldsites
report={'mapped_trees':len(state_for),'mapped_states':len(tree_for),'candidates':candidates,'rejected':rejected,'hits':hits,'seconds':time.monotonic()-start}
(out/'rotation_search_results.json').write_text(json.dumps(report,indent=2)+'\n')
print('DONE',len(candidates),'candidates',len(rejected),'structural exclusions',len(hits),'hits',time.monotonic()-start,flush=True)
