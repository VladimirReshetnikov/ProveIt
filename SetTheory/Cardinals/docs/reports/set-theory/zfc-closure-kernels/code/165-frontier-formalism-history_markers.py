#!/usr/bin/env python3
"""Finite backward-history marker proof. No sampling and no execution bound.

For each final (state,read) enumerate every length-d predecessor path and
solve all tape read/write constraints exactly. Merge their final symbolic
cells. Any concrete execution with at least d steps and that endpoint has
one listed path, so the common cells are a universal marker invariant.
Earlier blank prefixes are checked separately by the caller if needed.
"""
import argparse,json
from collections import defaultdict
from pathlib import Path

def read_table(p):
 t={}
 for line in Path(p).read_text().splitlines():
  a=line.split()
  if len(a)==5 and all(x.isdigit() for x in [a[0],a[1],a[2],a[4]]) and a[3] in ['L','R']:
   k=(int(a[0]),int(a[1]));assert k not in t
   t[k]=(int(a[2]),1 if a[3]=='R' else -1,int(a[4]))
 assert t
 return t

def histories(t,q,b,depth):
 incoming=defaultdict(list)
 for (s,r),a in t.items():incoming[a[2]].append((s,r,*a))
 paths=[]
 def walk(target,n,rev):
  if n:
   for e in incoming[target]:walk(e[0],n-1,rev+[e])
  else:
   path=rev[::-1];h=0;cells={};valid=True
   for s,r,w,d,dest in path:
    if h in cells and cells[h]!=r:valid=False;break
    cells[h]=w;h+=d
   if valid and (h not in cells or cells[h]==b):
    cells[h]=b;paths.append({'history':path,'final_cells':{i-h:v for i,v in cells.items()}})
 walk(q,depth,[])
 common={}
 if paths:
  common=dict(paths[0]['final_cells'])
  for p in paths[1:]:common={k:v for k,v in common.items() if p['final_cells'].get(k)==v}
 return {'target':[q,b],'depth':depth,'feasible_histories':len(paths),'common_cells':common,'histories':paths}

def main():
 a=argparse.ArgumentParser();a.add_argument('table');a.add_argument('--states',type=int,nargs='+',required=True);a.add_argument('--depth',type=int,default=5);a.add_argument('--output');p=a.parse_args();t=read_table(p.table)
 results=[histories(t,q,b,p.depth)for q in p.states for b in [0,1]]
 if p.output:Path(p.output).write_text(json.dumps({'table':str(p.table),'results':results},indent=2)+'\n')
 for r in results:print({k:v for k,v in r.items()if k!='histories'})
if __name__=='__main__':main()
