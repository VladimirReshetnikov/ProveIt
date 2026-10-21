#!/usr/bin/env python3
"""Broader finite-context fold search: all common-row pairs, two-sided windows.
Only exact positive stutter blocks count as hits. Limits are explicit.
"""
from pathlib import Path
from collections import defaultdict,Counter
import argparse,json,hashlib,time
from context_fold_search import read_table,backward_impossible


def contexts(table,start,states,radius,depth):
 pred=defaultdict(list)
 for(q,a),(w,d,n)in table.items():pred[n].append((q,a,w,d))
 result={};cert=[]
 for q in states:
  for a in(0,1):
   c={0:a}
   for pos in range(-radius,radius+1):
    if pos==0:continue
    for marker in(0,1):
     proof=backward_impossible(pred,start,q,{0:a,pos:1-marker},depth,10000)
     if proof is not None:
      assert pos not in c or c[pos]==marker
      c[pos]=marker;cert.append({'q':q,'read':a,'position':pos,'value':marker,**proof})
   result[q,a]=c
 return result,cert


def prove(table,p,q,a,co,entry,write,move,origin,steps_cap,cells_cap,nodes_cap):
 def phi(v):return p if v==q else v
 ow,od,og=table[origin,a]
 original=co[origin,a].copy();expected=original.copy();expected[0]=ow
 tape=original.copy();tape[0]=write
 stack=[(entry,move,tape,expected,0)];nodes=0;mx=0
 while stack:
  state,h,tape,expected,steps=stack.pop();nodes+=1
  if nodes>nodes_cap:return 'nodes',nodes,mx
  if state==phi(og) and h==od and tape==expected:
   mx=max(mx,steps+1);continue
  if steps>=steps_cap:return 'steps',nodes,mx
  if state==q or(state,0)not in table:return 'terminal',nodes,mx
  if h not in tape:
   if len(tape)>=cells_cap:return 'cells',nodes,mx
   for b in(0,1):
    t,e=tape.copy(),expected.copy();t[h]=e[h]=b
    stack.append((state,h,t,e,steps))
   continue
  b=tape[h]
  if state==p and b==a:w,d,n=write,move,entry
  else:w,d,n=table[state,b];n=phi(n)
  t=tape.copy();t[h]=w;stack.append((n,h+d,t,expected,steps+1))
 return 'PASS',nodes,mx


def main():
 ap=argparse.ArgumentParser();ap.add_argument('table',type=Path);ap.add_argument('--output',type=Path,required=True)
 ap.add_argument('--radius',type=int,default=4);ap.add_argument('--depth',type=int,default=12)
 ap.add_argument('--steps',type=int,default=96);ap.add_argument('--cells',type=int,default=14);ap.add_argument('--nodes',type=int,default=4096)
 z=ap.parse_args();t,start,states=read_table(z.table);beg=time.monotonic();co,cert=contexts(t,start,states,z.radius,z.depth)
 pairs=[]
 for i,p in enumerate(states):
  for q in states[i+1:]:
   for a in(0,1):
    if t[p,1-a]==t[q,1-a] and t[p,a]!=t[q,a]:pairs.append((p,q,a))
 stats=Counter();hits=[];nodes=0;trials=0
 for p,q,a in pairs:
  for write in(0,1):
   for move in(-1,1):
    for entry in states:
     if entry==q:continue
     trials+=1;r,n,mx=prove(t,p,q,a,co,entry,write,move,p,z.steps,z.cells,z.nodes);nodes+=n;stats[r]+=1
     if r!='PASS':continue
     r,n,my=prove(t,p,q,a,co,entry,write,move,q,z.steps,z.cells,z.nodes);nodes+=n;stats['second_'+r]+=1
     if r=='PASS':
      hits.append({'p':p,'q':q,'read':a,'entry':entry,'write':write,'move':move,'max_duration':max(mx,my),'context_p':co[p,a],'context_q':co[q,a]})
      print('HIT',hits[-1],flush=True)
 result={'sha256':hashlib.sha256(z.table.read_bytes()).hexdigest(),'start':start,'working_states':len(states),'pairs':pairs,'pair_count':len(pairs),'invariant_count':len(cert),'invariants':cert,'trials':trials,'symbolic_nodes':nodes,'stats':dict(stats),'hits':hits,'bounds':{'radius':z.radius,'backwards_depth':z.depth,'steps_after_first':z.steps,'visited_cells':z.cells,'nodes':z.nodes},'seconds':time.monotonic()-beg,'scope':'Only bounded exact context-corrected state-fold template; neither counterexamples to arbitrary optimization nor a state lower bound.'}
 z.output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items()if k not in('invariants','pairs')},indent=2))
if __name__=='__main__':main()
