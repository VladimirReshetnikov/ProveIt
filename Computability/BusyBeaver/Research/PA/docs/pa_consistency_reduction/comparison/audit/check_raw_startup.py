#!/usr/bin/env python3
"""Independent sparse-tape replay of a candidate's blank startup.

No symbolic runtime, native table numbering, compressed scan, or register oracle
is imported. The frame comparison is exact, including every nonzero tape cell.
"""
from pathlib import Path
import argparse,json,hashlib

def load(path):
 table={}
 for i,line in enumerate(Path(path).read_text().splitlines(),1):
  if not line.strip() or line.lstrip().startswith('#'):continue
  q,b,w,d,r=line.split();q,b,w,r=map(int,(q,b,w,r))
  if b not in(0,1)or w not in(0,1)or d not in('L','R'):raise ValueError(('bad row',i))
  if(q,b)in table:raise ValueError(('duplicate',q,b))
  table[q,b]=(w,1 if d=='R'else -1,r)
 states={q for q,b in table}
 if len(table)!=2*len(states):raise ValueError('table is not total on working states')
 return table

def frame_ones(path,gap=0,vs=None):
 if vs is None:vs=[0,0,0,0,0,0,2,0,0]+[1]*26
 if len(path)>48+gap:raise ValueError('path longer than header')
 out={-1}|{i for i,b in enumerate(path)if b};out.add(48+gap);at=49+gap
 for v in vs:
  at+=1
  for k in range(v+1):out.add(at+k)
  at+=v+1
 return out

def check(table_path,sites_path,root=75,start=0,budget=100000,expected_step=None):
 table=load(table_path);sites=json.loads(Path(sites_path).read_text());target=frame_ones(sites[25][0]);state=start;head=0;ones=set();visits=0
 for step in range(budget+1):
  if state==root:
   visits+=1
   if {x-head for x in ones}==target:
    if expected_step is not None and step!=expected_step:raise ValueError(('startup step differs',step,expected_step))
    return {'working_states':len(table)//2,'rows':len(table),'steps':step,'head':head,'root':root,'root_visits':visits,'relative_ones':sorted(target),'site25_path':sites[25][0],'table_sha256':hashlib.sha256(Path(table_path).read_bytes()).hexdigest(),'full_tape_match':True}
  row=table.get((state,int(head in ones)))
  if row is None:raise ValueError(('halt before startup',step,state,head))
  write,direction,state=row
  if write:ones.add(head)
  else:ones.discard(head)
  head+=direction
 raise ValueError(('startup budget exhausted',budget))

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('table');p.add_argument('sites');p.add_argument('--root',type=int,default=75);p.add_argument('--start',type=int,default=0);p.add_argument('--budget',type=int,default=100000);p.add_argument('--expected-step',type=int);a=p.parse_args()
 print(json.dumps(check(a.table,a.sites,a.root,a.start,a.budget,a.expected_step),indent=2))
