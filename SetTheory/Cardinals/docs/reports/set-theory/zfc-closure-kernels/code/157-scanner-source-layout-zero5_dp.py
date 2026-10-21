#!/usr/bin/env python3
"""Closed-forest interval beam DP with five-zero source constraint."""
from pathlib import Path
from functools import lru_cache
from collections import defaultdict
import sys,json,time,argparse
from grammar import Grammar,s

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--beam',type=int,default=2);a=ap.parse_args();a.out.mkdir(exist_ok=False)
 G=Grammar();rows=json.loads(a.source.read_text());oldtree=s.tree(rows);root=G.import_tree(oldtree);nbase=len(G.ns);started=time.monotonic();stats=defaultdict(int);BEAM=a.beam
 @lru_cache(None)
 def lead(n):return 0 if G.leaf(n)else 1+lead(G.ns[n][0])
 @lru_cache(None)
 def added(n):
  if n<nbase:return frozenset()
  return added(G.ns[n][0])|added(G.ns[n][1])|{n}
 def trim(xs):
  buckets=defaultdict(list)
  for n in set(xs):
   if G.bad[n][0]==0:buckets[lead(n)].append(n)
  return tuple(x for v in buckets.values()for x in sorted(v,key=lambda q:(len(added(q)),len(G.reachable(q)),q))[:BEAM])
 @lru_cache(None)
 def concat(n):return not G.leaf(n)and all(G.bds[x]==(0,0,False)for x in G.ns[n])
 @lru_cache(None)
 def forest(n):
  if G.bad[n][0]==0 and lead(n)<=4:return(n,)
  if concat(n):return forest(G.ns[n][0])+forest(G.ns[n][1])
  return(n,)
 @lru_cache(None)
 def repair(n,z):
  if z>5:return()
  if G.bad[n][z]==0:return(n,)
  if G.leaf(n):return(n,)
  if z==5:return()
  if not concat(n):
   A,B=G.ns[n];return trim(G.put((x,y))for x in repair(A,z+1)for y in repair(B,0))
  ff=list(forest(n))
  while len(ff)>1 and lead(ff[0])>4-z:
   if not concat(ff[0]):return()
   A,B=G.ns[ff[0]];ff[:1]=forest(A)+forest(B)
  if len(ff)==1:
   assert ff[0]!=n,('non-progress',n,z)
   return repair(ff[0],z)
  atoms=[repair(x,0)for x in ff];nn=len(atoms);stats['forests']+=1;stats['max_forest']=max(stats['max_forest'],nn)
  if nn>150:raise RuntimeError(('forest too large',nn))
  print('FOREST',n,'z',z,'atoms',nn,'bad',G.bad[n][0],'atom_leads',[lead(x)for x in ff],'choices',[len(x)for x in atoms],flush=True)
  cells={(i,i+1):trim(cands)for i,cands in enumerate(atoms)}
  for length in range(2,nn+1):
   for i in range(nn-length+1):
    j=i+length;c=[]
    for k in range(i+1,j):
     for l in cells[i,k]:
      if lead(l)>=5:continue
      for r in cells[k,j]:
       stats['joins']+=1;c.append(G.put((l,r)))
    cells[i,j]=trim(c)
  result=tuple(q for q in cells[0,nn]if lead(q)+z<=5)
  print('FOREST_RESULT',n,z,'choices',len(result),'added',[len(added(q))for q in result],flush=True)
  return result
 candidates=repair(root,0);saved=[]
 for i,n in enumerate(sorted(candidates,key=lambda q:len(G.reachable(q)))):
  tree=G.export(n);rr=s.sites(tree);met=s.metrics(tree);assert met['maximum_zero_run']<=5
  assert[x[1:]for x in rr]==[x[1:]for x in rows]
  assert s.graph_arithmetic(rr)[0]==s.graph_arithmetic(rows)[0]==s.graph_intervals(rr)
  dest=a.out/f'source-{met["dag_nodes"]}-{i}.json';dest.write_bytes(s.compact(rr))
  saved.append(dict(path=str(dest),metrics=met,first37_preserved=rr[:37]==rows[:37]))
 result=dict(status='BEAM_DP_FINISHED',stats=dict(stats),nodes_created=len(G.ns),seconds=time.monotonic()-started,beam=BEAM,saved=saved)
 (a.out/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
if __name__=='__main__':main()
