#!/usr/bin/env python3
"""Exploratory condensed-detachment calibration of small implication bases."""
from restricted_lukasiewicz import C,size,canonical,detach,subsumes,polish
from pathlib import Path
import argparse,heapq,json,time


def run(basis,maxsize,maxsteps,seconds):
 a,b,c=0,1,2
 K=C(a,C(b,a));P=C(C(C(a,b),a),a)
 H=C(C(a,b),C(C(b,c),C(a,c)))
 G=C(C(C(a,b),a),C(c,a))
 axioms={'KPH':[K,P,H],'GH':[G,H],'GK':[G,K],'GP':[G,P], 'G':[G], 'GqH':[C(C(C(a,b),a),C(b,a)),H], 'GaH':[C(C(C(a,b),a),C(a,a)),H], 'GPxH':[C(c,P),H]}[basis]
 targets={'I':C(a,a),'K':K,'P':P,'H':H,
          'S':C(C(a,C(b,c)),C(C(a,b),C(a,c))),
          'L':C(C(C(c,3),a),C(C(a,c),C(b,c)))}
 nodes=[];known={};pending=[];processed=[];found={};start=time.monotonic()
 def add(t,proof):
  if t is None or size(t)>maxsize or t in known:return
  if any(size(u)<=size(t) and subsumes(u,t)for u in known):return
  i=len(nodes);known[t]=i;nodes.append((t,proof));heapq.heappush(pending,(size(t),i))
  for name,target in targets.items():
   if name not in found and subsumes(t,target):
    found[name]=i;print('FOUND',name,i,polish(t),flush=True)
 for ax in axioms:add(canonical(ax),'axiom')
 while pending and len(processed)<maxsteps and time.monotonic()-start<seconds:
  _,i=heapq.heappop(pending);x=nodes[i][0]
  for j in processed+[i]:
   y=nodes[j][0];add(detach(x,y),[i,j])
   if i!=j:add(detach(y,x),[j,i])
  processed.append(i)
  if len(processed)%100==0:print('PROGRESS',len(processed),len(nodes),round(time.monotonic()-start,1),flush=True)
  if {'K','P','H'}<=found.keys() and basis!='KPH':break
  if 'L'in found:break
 for t,p in nodes:
  if p!='axiom':assert detach(nodes[p[0]][0],nodes[p[1]][0])==t
 result=dict(basis=basis,maxsize=maxsize,maxsteps=maxsteps,seconds=time.monotonic()-start,processed=len(processed),nodes=len(nodes),found=found,
             derivations=[dict(formula=polish(t),term=t,proof=p)for t,p in nodes])
 (Path(__file__).parent/('small_basis_'+basis+'.json')).write_text(json.dumps(result,indent=2)+'\n')
 print('DONE',{k:v for k,v in result.items()if k!='derivations'},flush=True)

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--basis',default='GH');ap.add_argument('--maxsize',type=int,default=31);ap.add_argument('--maxsteps',type=int,default=2000);ap.add_argument('--seconds',type=float,default=180)
 args=ap.parse_args();run(args.basis,args.maxsize,args.maxsteps,args.seconds)
