"""Jointly pay for several new history selectors and save reader states.

This is a bounded layout search, not a proof or a global lower bound.
"""
import sys, json, itertools, time
from pathlib import Path
from collections import defaultdict
import numpy as np
from scipy.optimize import milp, Bounds, LinearConstraint
from scipy.sparse import coo_matrix
P=Path('support/work/optimize196')
sys.path.insert(0,str(P))
from layout import *

def solve(grammar, limit=120, helpers=4):
 t=read_grammar(grammar); rows,index,shape=build(t)
 inc=defaultdict(set)
 for (q,b),(w,d,n) in rows.items():
  if d and w==b and n in shape:inc[n].add(b)
 left=[q for q in shape if inc[q]=={0}];right=[q for q in shape if inc[q]=={1}]
 providers=[defaultdict(list),defaultdict(list)]
 for q in {q for q,b in rows}:
  for bit in (0,1): providers[bit][rows[q,bit]].append(q)
 existing=defaultdict(set)
 for a,b,opts in opportunities_fast(rows,shape):
  existing[a,b]=True
 directprov=[defaultdict(list),defaultdict(list)]
 for h in {q for q,b in rows}:
  w0,d0,u0=rows[h,0];w1,d1,u1=rows[h,1]
  if w0 or w1!=1 or not d0 or not d1:continue
  for bit in (0,1):
   if (u0,bit) in rows and (u1,bit) in rows:directprov[bit][(rows[u0,bit],rows[u1,bit])].append((h,u0,u1))
 edges=[];all_h=set()
 for a in left:
  for b in right:
   req=[];valid=True
   for bit in (0,1):
    if rows[a,bit]==rows[b,bit]:req.append(None);continue
    old=[z for z in directprov[bit].get((rows[a,bit],rows[b,bit]),[]) if not {a,b}&set(z)]
    if old:req.append(None);continue
    uv={(u,v) for u in providers[bit][rows[a,bit]] for v in providers[bit][rows[b,bit]] if not {a,b}&{u,v}}
    if not uv:valid=False;break
    req.append(uv)
   if valid:
    edges.append((a,b,req))
    for hs in req:
     if hs:all_h.update(hs)
 hs=sorted(all_h);hid={h:i+len(edges) for i,h in enumerate(hs)}
 print('catalog',len(shape),len(edges),len(hs),'baseline folds',len(max_matching(opportunities_fast(rows,shape))),flush=True)
 data=[];ri=[];ci=[];lo=[];hi=[]
 def constraint(terms,up,low=-np.inf):
  i=len(lo)
  for c,v in terms:ri.append(i);ci.append(c);data.append(v)
  lo.append(low);hi.append(up)
 uses=defaultdict(list)
 for i,(a,b,req) in enumerate(edges):
  uses[a].append(i);uses[b].append(i)
  for opts in req:
   if opts is not None:constraint([(i,1)]+[(hid[h],-1) for h in opts],0)
 for q,es in uses.items():constraint([(e,1) for e in es],1)
 for h in hs:
  for bit,q in enumerate(h):
   if q in shape and inc[q]!={bit}:
    constraint([(hid[h],1)]+[(e,1) for e in uses[q]],1)
 constraint([(hid[h],1) for h in hs],helpers)
 n=len(edges)+len(hs)
 objective=np.array([-1.]*len(edges)+[1.]*len(hs))
 matrix=coo_matrix((data,(ri,ci)),shape=(len(lo),n)).tocsc()
 matrix.indices=matrix.indices.astype(np.int32);matrix.indptr=matrix.indptr.astype(np.int32)
 print('solving',matrix.shape,'nnz',matrix.nnz,flush=True)
 res=milp(objective,integrality=np.ones(n),bounds=Bounds(np.zeros(n),np.ones(n)),constraints=LinearConstraint(matrix,lo,hi),options={'time_limit':limit,'mip_rel_gap':0.,'disp':False})
 summary={'message':res.message,'grammar':str(grammar),'edge_count':len(edges),'helper_candidates':len(hs),'fun':float(res.fun) if res.fun is not None else None,'mip_dual_bound':float(res.mip_dual_bound) if res.fun is not None else None}
 if res.x is not None:
  summary['folds']=[(a,b) for i,(a,b,req) in enumerate(edges) if res.x[i]>.5]
  summary['helpers']=[h for h in hs if res.x[hid[h]]>.5]
  summary['states_relaxed']=len(rows)//2+len(summary['helpers'])-len(summary['folds'])
 print(json.dumps(summary),flush=True)
 Path(__file__).with_name('milp_'+Path(grammar).stem+'.json').write_text(json.dumps(summary,indent=2))
 if res.x is None:return
 new=dict(rows)
 for i,(u,v) in enumerate(summary['helpers']):new[3000+i,0]=(0,True,u);new[3000+i,1]=(1,True,v)
 pairs=summary['folds']
 for order in [pairs,list(reversed(pairs))]:
  rr=dict(new);ss=dict(shape);done=[]
  for a,b in order:
   ops=opportunities_fast(rr,ss)
   opts=next((o for x,y,o in ops if (x,y)==(a,b)),None)
   if opts is None:break
   acts=[o[0] for o in opts];rr=fold(rr,a,b,acts);ss.pop(a);done.append((a,b,acts))
  print('realized',len(done),'of',len(pairs),flush=True)
  if len(done)==len(pairs):
   cs=source(t)[2];ans=validate(rr,cs);print('VALIDATION',len(rr)//2,ans,flush=True)
   if ans['ok'] and len(rr)//2<196:
    Path(__file__).with_name('multi_selector_candidate.json').write_text(json.dumps({'rows':[[q,b,*a] for (q,b),a in sorted(rr.items())],'folds':done,'validation':ans},indent=2))
 if __name__=='_unused_':pass


if __name__=='__main__':
 for p in sorted(Path(__file__).with_name('fused_unconditional').glob('assembled_*.json')):
  if json.loads(p.read_text())['cost'][0] <= 65:solve(p, 10)
