#!/usr/bin/env python3
"""Conservative clear-loop-aware register liveness of the GH source CFG.
No claim of semantic minimality is made; masks are a sound 0/positive abstraction.
"""
from pathlib import Path
from collections import deque
import json,itertools,time
base=Path(__file__).resolve().parent/'gh_input'
ins=json.loads((base/'instructions.json').read_text());sites=json.loads((base/'sites.json').read_text())
names=['N','T','W','A','D','H','X','Y','L']
# A decrement loop whose positive arm reaches itself through jumps only is
# the exact total assignment r:=0, irrespective of its incoming natural value.
clears={}
for i,x in enumerate(ins):
 if x[0]!='dec':continue
 _,r,z,p=x;j=p;seen=set()
 while j not in seen and ins[j][0]=='jump':
  seen.add(j);j=ins[j][1]
 if j==i:clears[i]=(r,z,sorted(seen))
print('clear loops',len(clears),flush=True)
# Conservative syntactic liveness after summarizing those total clears.
N=len(ins);successors=[];uses=[];defs=[]
for i,x in enumerate(ins):
 if i in clears:r,z,_=clears[i];successors.append([z]);uses.append(0);defs.append(1<<r)
 elif x[0]=='inc':successors.append([x[2]]);uses.append(1<<x[1]);defs.append(1<<x[1])
 elif x[0]=='dec':successors.append(x[2:]);uses.append(1<<x[1]);defs.append(1<<x[1])
 elif x[0]=='jump':successors.append([x[1]]);uses.append(0);defs.append(0)
 else:successors.append([]);uses.append(0);defs.append(0)
preds=[[]for _ in ins]
for i,ss in enumerate(successors):
 for j in ss:preds[j].append(i)
live=[0]*N;queue=deque(range(N));queued=set(range(N))
while queue:
 i=queue.popleft();queued.remove(i);out=0
 for j in successors[i]:out|=live[j]
 v=uses[i]|(out&~defs[i])
 if v!=live[i]:
  live[i]=v
  for j in preds[i]:
   if j not in queued:queued.add(j);queue.append(j)
# Reachable 0/positive states from the canonical logical seed N=2,others0.
start=(25,1);todo=deque([start]);seen={start};parent={start:None}
while todo:
 i,mask=todo.popleft();x=ins[i]
 if i in clears:r,z,_=clears[i];nexts=[(z,mask&~(1<<r))]
 elif x[0]=='inc':nexts=[(x[2],mask|(1<<x[1]))]
 elif x[0]=='dec':
  _,r,z,p=x;b=1<<r
  nexts=[(p,mask),(p,mask&~b)]if mask&b else[(z,mask)]
 elif x[0]=='jump':nexts=[(x[1],mask)]
 else:nexts=[]
 for nxt in nexts:
  if nxt not in seen:seen.add(nxt);todo.append(nxt);parent[nxt]=(i,mask)
# Ignore known-zero variables for the interference witness; numerical values
# simultaneously positive AND syntactically live still need distinct cells
# for direct overlay under this abstraction.
edges={};maxset=0;maxstate=None;hist={}
for pc,mask in sorted(seen):
 active=mask&live[pc];n=active.bit_count();hist[n]=hist.get(n,0)+1
 if n>maxset:maxset=n;maxstate=(pc,mask)
 regs=[r for r in range(9)if active>>r&1]
 for a,b in itertools.combinations(regs,2):edges.setdefault((a,b),(pc,mask))
path=[];p=maxstate
while p is not None:path.append(p);p=parent[p]
path.reverse()
result={'source':'PA194GH','source_sites':N,'clear_loop_entries':len(clears),
 'clear_loops':[{'pc':i,'register':r,'zero_exit':z,'positive_jump_chain':s}for i,(r,z,s)in clears.items()],
 'reachable_abstract_states':len(seen),'reachable_sites':len({p for p,m in seen}),
 'max_positive_and_live':maxset,'max_witness':{'pc':maxstate[0],'mask':maxstate[1],'instruction':ins[maxstate[0]],'path':sites[maxstate[0]][0],'registers':[names[r]for r in range(9)if(maxstate[1]&live[maxstate[0]])>>r&1]},
 'histogram':hist,'interference_edges':[{'registers':[names[a],names[b]],'pc':p,'mask':m}for(a,b),(p,m)in sorted(edges.items())],
 'abstract_witness_path_length':len(path),'all_nine_form_clique':len(edges)==36,
 'scope':'Conservative static liveness with exact total clear loops, restricted by sound reachable0/positive masks. It rules out an8-cell static coloring of THIS abstraction, not semantic register reuse, source transformations, or a different encoding.'}
Path('gh_liveness.json').write_text(json.dumps(result,indent=2)+'\n')
Path('gh_liveness_witness.json').write_text(json.dumps(path)+'\n')
print(json.dumps({k:v for k,v in result.items()if k not in('clear_loops','interference_edges')},indent=2))
