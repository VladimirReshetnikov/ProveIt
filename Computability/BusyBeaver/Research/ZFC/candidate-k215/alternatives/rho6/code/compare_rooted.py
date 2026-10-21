#!/usr/bin/env python3
"""Exact rooted action-labelled deterministic transition graph comparison.
Reachability makes any state bijection fixing start uniquely forced.
"""
from pathlib import Path
from collections import deque
import argparse,json,hashlib

def read(p):
 t={};start=None
 for l in p.read_text().splitlines():
  if l.startswith('#! start '):start=int(l.split()[-1])
  elif l and not l.startswith('#'):
   q,b,w,d,z=l.split();t[int(q),int(b)]=(int(w),d,int(z))
 assert start is not None
 return t,start

def compare(A,ast,B,bst):
 mp={ast:bst};inv={bst:ast};paths={ast:''};todo=deque([ast])
 while todo:
  q=todo.popleft();r=mp[q];p=paths[q]
  for b in(0,1):
   a=A.get((q,b));z=B.get((r,b))
   if a is None or z is None:
    if a!=z:return {'isomorphic':False,'reason':'terminal mismatch','word':p+str(b),'left_state':q,'right_state':r}
    continue
   if a[:2]!=z[:2]:return {'isomorphic':False,'reason':'action mismatch','word':p+str(b),'left_state':q,'right_state':r,'left':a,'right':z}
   x,y=a[2],z[2]
   if x in mp and mp[x]!=y:return {'isomorphic':False,'reason':'forced state map conflict','word':p+str(b),'left_target':x,'old_right_target':mp[x],'new_right_target':y}
   if y in inv and inv[y]!=x:return {'isomorphic':False,'reason':'forced injectivity conflict','word':p+str(b),'right_target':y,'old_left_target':inv[y],'new_left_target':x}
   if x not in mp:mp[x]=y;inv[y]=x;paths[x]=p+str(b);todo.append(x)
 qa={q for q,b in A};qb={q for q,b in B};assert qa<=set(mp)and qb<=set(inv)
 return {'isomorphic':True,'map':mp,'reachable_working_states':len(qa)}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--candidate',type=Path,required=True);ap.add_argument('--reference',type=Path,action='append',required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();A,ast=read(a.candidate)
 res=[]
 for p in a.reference:
  B,bst=read(p);res.append({'reference':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),**compare(A,ast,B,bst)})
 r={'candidate':str(a.candidate),'candidate_sha256':hashlib.sha256(a.candidate.read_bytes()).hexdigest(),'comparisons':res,'scope':'State renaming only, with initial state fixed and read/write/move actions preserved; includes terminal graph states. Not a statement of behavioral inequivalence.'};a.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
if __name__=='__main__':main()
