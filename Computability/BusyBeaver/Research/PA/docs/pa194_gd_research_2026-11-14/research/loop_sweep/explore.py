#!/usr/bin/env python3
"""Replay the corrected, collision-free forty-candidate loop sweep.

The recorded `lower` field is an optimistic raw-minus-matching count, not a
lower bound on arbitrary machines. Every candidate must preserve the complete
resolved source graph. Fresh helper labels never overwrite existing controls.
"""
import sys,json,functools,itertools,argparse
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'construction'))
import compiler as c
import support
class Local:
    read_table=staticmethod(support.read_table)
    @staticmethod
    def reachable(rows):
        seen=set();todo=[74]
        while todo:
            q=todo.pop()
            if q==254 or q in seen:continue
            assert (q,0) in rows and (q,1) in rows, ('undefined target',q)
            seen.add(q)
            todo.extend(rows[q,b][2] for b in (0,1))
        return {k:v for k,v in rows.items() if k[0] in seen}
lc=Local()
I=('leaf','inc',1)
def tup(x):return tuple(map(tup,x)) if isinstance(x,list) else x
@functools.cache
def trees(n):
 if n==1:return (I,)
 return tuple((a,b) for i in range(1,n) for a in trees(i) for b in trees(n-i))
def tail(t,d=0):
 if t==I:return ('leaf','continueTo',d+1)
 return (t[0],tail(t[1],d+1))
def allowed(rows):
 inc={q:set() for q,_ in rows}
 for (q,b),(w,d,n) in rows.items():
  if n in inc:inc[n].add((w,d))
 return {q:() for q in inc if inc[q] in ({(0,True)},{(1,True)}) and q!=74}
def compile_loop(base,tree):
 rows={k:v for k,v in base.items() if k[0] not in (139,190)}
 signatures={(rows[q,0],rows[q,1]):q for q,_ in rows}
 ids={}; fresh=500
 def action(t,bit):
  nonlocal fresh
  if t==I:return bit,True,61
  if t[0]=='leaf':
   assert t[1]=='continueTo' and t[2] in (2,3)
   return (0,False,16) if t[2]==2 else (1,False,73)
  if t in ids:return bit,True,ids[t]
  pair=(action(t[0],0),action(t[1],1))
  q=signatures.get(pair)
  if q is None:
   while (fresh,0) in rows:fresh+=1
   q=fresh;fresh+=1;rows[q,0],rows[q,1]=pair;signatures[pair]=q
  ids[t]=q;return bit,True,q
 rows[139,0]=action(tree[0],0);rows[139,1]=action(tree[1],1)
 return lc.reachable(rows)
def run():
 report=[]
 for name,folder in [('PA194AX11GH',HERE/'inputs/AX11GH'),('PA194AX11GHS',HERE/'inputs/AX11GHS'),('PA194',HERE/'inputs/primary'),('AX11H',HERE/'inputs/AX11H')]:
  raw=lc.read_table(folder/'raw.native.tm')
  ns={k:tup(v) for k,v in json.loads((folder/'nodes.json').read_text()).items()}
  gp=folder/'grammar.tree.json'
  g=tup(json.loads(gp.read_text())) if gp.exists() else c.read_grammar(folder/'grammar.json')
  c.machine=lambda:(raw,[]);c.raw_nodes=lambda:ns
  oldsites,oldins,_=c.source(g)
  for i,tree in enumerate(trees(5)):
   tree=tail(tree)
   q=tree
   while q[0]!='leaf':q=q[1]
   if q[2]>3:continue
   rows=compile_loop(raw,tree)
   if any(n!=254 and (n,0) not in rows for w,d,n in rows.values()):continue
   # Erase unused original four-increment macro; literals retained inside AX tree are rebuilt.
   nn=dict(ns);nn['node62']=tree;c.raw_nodes=lambda:nn
   sites,ins,cs=c.source(g)
   assert oldins==ins,(name,i)
   shape=allowed(rows)
   ops=c.opportunities_fast(rows,shape)
   pairs=c.max_matching(ops)
   rec=dict(name=name,index=i,tree=tree,raw=len(rows)//2,folds=len(pairs),lower=len(rows)//2-len(pairs),ops=[(a,b) for a,b,_ in ops],pairs=pairs)
   report.append(rec)
 assert len(report)==40
 return report

if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--output',type=Path,required=True)
 p.add_argument('--check-recorded',action='store_true')
 a=p.parse_args();report=run()
 if a.check_recorded:assert json.loads(json.dumps(report))==json.loads((HERE/'report.json').read_text()), 'Corrected report differs'
 a.output.parent.mkdir(parents=True,exist_ok=True)
 a.output.write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps(dict(candidates=len(report),minimum_optimistic_controls=min(x['lower']for x in report),
                      source_graphs_equal=True,recorded_report_matched=a.check_recorded)))
