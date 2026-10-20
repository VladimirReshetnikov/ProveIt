"""Experimental fixed-PC primitive interfaces on an arbitrary native table.

Temporary decoder labels are disjoint from new native219 labels 301/302.
Each successful test is universal in natural register values for its literal
source address. It does not generalize untested address-prefix contexts.
"""
from pathlib import Path
import inspect,json,sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'source_work'));import rotation_search as r
BASE=ROOT/'k219_replay/parent_replay/baseline/K221_Construction_2026-10-20'
sys.path.insert(0,str(BASE/'portable/runtime/vendor'));import symbolic_runtime as rt
class Probe:
 def __init__(self,table=None):
  self.T=r.b.read_table((ROOT/'baseline219/K219_Construction_2026-10-20/machine/k219.native.tm').read_bytes())if table is None else table
  self.mp={int(q):int(v)for q,v in json.loads((BASE/'portable/runtime/reference_results/legacy_mapping.json').read_text()).items()}
  for q in{q for q,b in self.T}|{254}:
   if q not in self.mp:self.mp[q]=q+1000
  assert len(set(self.mp.values()))==len(self.mp)
  self.L={(self.mp[q],b):(w,d,self.mp[z])for(q,b),(w,d,z)in self.T.items()}
  self.lemmas,_=rt.prove_blocks(self.L)
  source=inspect.getsource(rt.case).replace('def case(','def limited_case(').replace('range(4000)','range(1000)')
  env=dict(vars(rt));exec(source,env);self.case=env['limited_case']
 def table(self,pc,action):
  N=dict(self.L)
  assert max(self.mp.values())<3000
  for i,bb in enumerate(pc):
   q=96 if i==0 else 3000+i
   for bit in(0,1):N[q,bit]=(bit,1,254)
   if i==len(pc)-1:
    w,d,z=action;N[q,int(bb)]=(w,d,self.mp[z])
   else:N[q,int(bb)]=(int(bb),1,3001+i)
  return N
 def test(self,pc,op,arg,action):
  N=self.table(pc,action)
  try:
   for pos in((False,True)if op=='CD'else(False,)):
    self.case(N,self.lemmas,[pc,op,arg],pos)
  except(AssertionError,KeyError):return False
  return True
