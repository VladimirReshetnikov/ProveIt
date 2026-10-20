#!/usr/bin/env python3
"""Build source-level additive-binder variants from the K220 source.
Research only: compilation is decoder binding, not full runtime verification.
"""
from pathlib import Path
import os,sys,json
from functools import cache
ROOT=Path(os.environ.get('CALCULUS_WORK_ROOT',Path.cwd()/'calculus_runs')).resolve()
if 'K220_BASE' not in os.environ or 'K221_BASE' not in os.environ:
 raise RuntimeError('Run through run_experiment.py, or set K220_BASE and K221_BASE to extracted pinned packets.')
BASE=Path(os.environ['K220_BASE']).resolve()
os.environ['ENCODING_OUTPUT']=str(ROOT/'research_calculus/generated')
sys.path.insert(0,str(BASE/'research/encoding/scripts'))
from recompile import s,b,compile_tree
ROWS=json.loads((BASE/'machine/sites220.json').read_text());TREE=s.tree(ROWS)
T=b.read_table((BASE/'machine/k220.native.tm').read_bytes())
GROUPS,_=b.decoder_map(T,TREE)
q=lambda n:b.sole(GROUPS,n)
A=q(98);B=q(12);INC=('CI',1)
PATH='1110100100111000010'
OLD=s.subtree(TREE,PATH)
@cache
def flat(n):return (n,)if s.leaf(n)else flat(n[0])+flat(n[1])
assert flat(OLD)==flat(A)+flat(B)+flat((q(90),INC))
assert s.boundary(A[1])==s.boundary(B[1])==(0,0,False)

def serial(xs):
 n=xs[-1]
 for x in reversed(xs[:-1]):n=(x,n)
 return n

def runmacro(node,regs,limit=3000000):
 # Append a CH to turn macro exit into an observable stop.
 rr=s.sites((node,('CH',None)));gg=s.graph_arithmetic(rr)[0];assert gg==s.graph_intervals(rr)
 pc=0;r=list(regs)
 for k in range(limit):
  eff,tg=gg[pc];op=eff[0]
  if op=='halt':return r,k
  if op=='increment':r[eff[1]]+=1;pc=tg[0]
  elif op=='decrement':
   v=r[eff[1]];r[eff[1]]=max(0,v-1);pc=tg[bool(v)]
  else:pc=tg[0]
 raise RuntimeError('timeout')

if __name__=='__main__':
 OUT=ROOT/'research_calculus/generated/additive';OUT.mkdir(parents=True,exist_ok=True)
 res=[]
 for order in ['ab','ba']:
  first,other=(A,B)if order=='ab'else(B,A)
  for assoc in ['right','left']:
   n=(first,(other[1],INC))if assoc=='right'else((first,other[1]),INC)
   assert s.boundary(n)==(0,0,False)
   checks=0
   for av in range(5):
    for bv in range(5):
     for top,stack in [(0,0),(1,0),(2,3)]:
      regs=[7,top,stack,4,av,bv,0,0,2]
      got,_=runmacro(n,regs)
      want=regs.copy();want[1]=av+bv+1;want[2]=(top+stack)*(top+stack+1)//2+stack
      assert got==want,(order,assoc,av,bv,got,want)
      checks+=1
   new=s.replace(TREE,PATH,n);rr=s.sites(new);gg=s.graph_arithmetic(rr)[0];assert gg==s.graph_intervals(rr)
   nm=order+'_'+assoc;d=OUT/nm;d.mkdir(exist_ok=True)
   (d/'sites.json').write_bytes(s.compact(rr))
   r={'name':nm,'metrics':s.metrics(new),'macro_metrics':s.metrics(n),'macro_tests':checks,'logical_kappa':'a+b+1','path':PATH}
   try:
    tt,m=compile_tree(T,TREE,new);r['compile']=m;(d/'candidate.tm').write_bytes(b.table_bytes(tt))
   except Exception as e:r['error']=repr(e)
   (d/'receipt.json').write_text(json.dumps(r,indent=2)+'\n');res.append(r);print(json.dumps(r),flush=True)
 (OUT/'summary.json').write_text(json.dumps(res,indent=2)+'\n')
