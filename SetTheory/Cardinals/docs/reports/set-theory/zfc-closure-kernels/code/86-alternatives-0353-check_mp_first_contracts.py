#!/usr/bin/env python3
"""Exact finite register tests of the new MP-first-falsity code. Not an unbounded proof."""
from pathlib import Path
import importlib,sys,json,itertools,time
HERE=Path(__file__).resolve().parent;R=HERE.parent/'source/Computability/BusyBeaver/Research/ZFC'
sys.path[:0]=[str(R),str(HERE/'mp_first/backend')]
import recover_wade_dag as r
from pairing_backend_experiment import execute_helper
import TMBuilder as b
nodes,names=r.parse_dag(r.git_bytes(None,'ZF/m254/coq/prog/Dag254.v').decode())
nodes[147]=('ENode 148','ENode 170');nodes[130]=('ENode 123','ENode 219')
nodes[219]=('ENode 198','ENode 220');nodes[220]=('EInc 5','ENode 132')
names[219]='mp_goal_copy_and_test';names[220]='mp_goal_one_test'
builder=r.builder_from_dag(b,nodes,names)
def P(x,y):return (x+y)*(x+y+1)//2+y
def unP(n):
 import math
 s=(math.isqrt(8*n+1)-1)//2;y=n-s*(s+1)//2;return s-y,y
counts={};start=time.monotonic()
for d,s in itertools.product(range(8),range(6)):
 vals=[101,0,s,0,d,0,0,0,103];out=execute_helper(builder,219,vals)
 if d==1:assert out==('halt',)
 else:assert out==('normal',) and vals==[101,d,s,0,0,0,0,0,103],(d,s,out,vals)
counts['goal_copy_test']=48
count=0
for t,d,s,success in itertools.product(range(7),range(7),range(5),[False,True]):
 h=4*P(t,d)+(0 if success else 1);vals=[101,t,s,0,d,h,0,0,103]
 out=execute_helper(builder,150,vals)
 if success and d==1:assert out==('halt',)
 else:
  expected=[101,d if success else 0,s,0,0 if success else d,0,0,0,103]
  assert out==('normal',) and vals==expected,(t,d,s,success,out,vals,expected)
 count+=1
counts['complete_MP']=count
count=0
for t,s,d,h in itertools.product(range(3),range(26),range(3),range(4)):
 vals=[101,t,s,0,d,h,0,0,103];out=execute_helper(builder,147,vals);head,tail=unP(s)
 assert out==('normal',) and vals==[101,t,tail,0,d,h+head,0,0,103],(t,s,d,h,out,vals)
 count+=1
counts['raw_nip147']=count
# WARNING: pop(param2) is additive, so direct170 does not clear incoming H.
# The old NIP's equality test cleared H as a necessary side effect.
print('Raw direct-pop variant leaves H+stackhead; it is not the intended unconditional replacement.')
print(json.dumps(dict(status='DETECTED_SEMANTIC_DEFECT',cases=counts,seconds=time.monotonic()-start),indent=2))
(HERE/'mp_first_contract_tests.json').write_text(json.dumps(dict(status='DETECTED_SEMANTIC_DEFECT',cases=counts,defect='Replacing147.right by170 leaves oldH added to poppedhead; oldequalitytest clearedH as sideeffect.',seconds=time.monotonic()-start),indent=2)+'\n')
