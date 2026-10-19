#!/usr/bin/env python3
"""Bounded safe-associativity search on genuinely changed program semantics."""
from pathlib import Path
import sys,json,random,math,time,argparse
H=Path(__file__).resolve().parent;R=H.parent/'context_folds/recovered/67/research'
sys.path[:0]=[str(R/'sources/beyond252/beyond252/exploratory/vendor'),str(R/'agent_logic')]
import rotate_search as rs
from verify_reassociation import Decoder,read_json
ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=H/'mp_first_from201.json');ap.add_argument('--iterations',type=int,default=100000);ap.add_argument('--name',default='mp_first');ap.add_argument('--maxdepth',type=int,default=40);a=ap.parse_args()
n,r,_=read_json(a.input);base=Decoder(n,r);normal=base.normal(('N',r));graph=base.graph();best=(len(n),base.metrics()[1],base.metrics()[2]);bestn,bestr=n,r
rng=random.Random(20261018);t=time.monotonic();updates=[]
for restart in range(5):
 cur,root=bestn,bestr
 for i in range(a.iterations):
  opts=[o for o in rs.options(cur) if o[2]!='commute_increments'];q,exp,kind=rng.choice(opts);nn,nr=rs.mutate(cur,root,q,exp);m=rs.zero_metrics(nn,nr)
  if m[1]>7 or m[2]>a.maxdepth:continue
  cost=len(nn)-len(cur);temp=.03+.5*(1-i/a.iterations)
  if cost<=0 or rng.random()<math.exp(-cost/temp):cur,root=nn,nr
  m=rs.zero_metrics(cur,root);key=(len(cur),m[1],m[2])
  if key<best:
   d=Decoder(cur,root);assert d.normal(('N',root))==normal and d.graph()==graph
   best=key;bestn,bestr=cur,root;updates.append([restart,i,*key]);print(updates[-1],flush=True)
   (H/f'{a.name}_rotated_best.json').write_text(json.dumps(dict(root=root,nodes=cur),indent=2)+'\n')
 d=Decoder(bestn,bestr);assert d.normal(('N',bestr))==normal and d.graph()==graph
 (H/f'{a.name}_rotation_report.json').write_text(json.dumps(dict(status='RUNNING' if restart<4 else 'DONE',completed_restarts=restart+1,best=best,iterations_per_restart=a.iterations,updates=updates,seconds=time.monotonic()-t,exact_ordered_normal_form_and_guarded_graph_equal=True),indent=2)+'\n')
 print('restart',restart,'best',best,'seconds',time.monotonic()-t,flush=True)
