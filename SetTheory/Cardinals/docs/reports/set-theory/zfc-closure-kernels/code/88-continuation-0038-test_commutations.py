#!/usr/bin/env python3
"""Generate reviewed closed-register-disjoint swaps with transported colors.
Both operands are syntactically halt-free; partial normal relations commute.
"""
from pathlib import Path
from functools import cache
import sys,json,collections
sys.path.insert(0,str(Path(__file__).parent));import colored_merge_search as s
OUT=s.OUT
@cache
def bounds(n):
 e=s.r.entries[n]
 if e[0]=='N':
  ba,ca,ra,ha=bounds(e[1]);bb,cb,rb,hb=bounds(e[2]);return max(0,ba-1,bb),max(0,ca,cb-1),ra|rb,ha or hb
 return (1 if e[0]=='CD' else e[1] if e[0]=='CB' else 0,e[1] if e[0]=='CC' else 0,frozenset([e[1]]) if e[0] in ('CI','CD') else frozenset(),e[0]=='CH')

def transform(root,roles,pivots):
 outroles={};memo={};collisions=[];proof=[]
 def add(n,q):
  if n in outroles and outroles[n]!=q:collisions.append((n,outroles[n],q))
  else:outroles[n]=q
 def rec(n):
  if n in memo:return memo[n]
  e=s.r.entries[n]
  if e[0]!='N':return n
  a,b=rec(e[1]),rec(e[2])
  if roles[n] in pivots:
   ba,ca,ra,ha=bounds(a);bb,cb,rb,hb=bounds(b)
   assert not(ba or ca or bb or cb or ra&rb or ha or hb)
   proof.append(dict(old_node=n,old_children=[e[1],e[2]],physical_color=roles[n],left_registers=sorted(ra),right_registers=sorted(rb),left_closed=True,right_closed=True,both_halt_free=True))
   a,b=b,a
  nn=s.r.mk(('N',a,b));add(nn,roles[n]);memo[n]=nn;return nn
 rr=rec(root);return rr,outroles,collisions,proof

def build(qs):
 root,roles,coll,proof=transform(s.base,s.C0,qs)
 T=s.c.T.copy();E=s.r.entries
 for n,q in roles.items():
  if q not in qs:continue
  for b in (0,1):
   ch=E[E[n][b+1]]
   if ch[0]=='N':row=(b,'R',roles[E[n][b+1]])
   else:
    assert ch[0]=='CI'
    generic={0:18,1:70,2:65,3:201,4:169,5:72,6:39,7:93,8:47}
    row=(b,'R',generic[ch[1]])
   T[q,b]=row
 name='commute_'+'_'.join(map(str,qs))
 s.r.dump_graph(root,OUT/(name+'.json'),dict(source_pairs=len(s.r.reachable(root)),proof=proof,collisions=coll,proof_status='ordinary local closed disjoint halt-free swaps; binary audit separate'))
 s.c.save_table(T,OUT/(name+'.tm'));(OUT/(name+'_roles.json')).write_text(json.dumps({'roles':roles})+'\n')
 print(name,'pairs',len(s.r.reachable(root)),'collisions',coll)
if __name__=='__main__':
 for qs in [(106,),(253,),(106,253)]:build(qs)
