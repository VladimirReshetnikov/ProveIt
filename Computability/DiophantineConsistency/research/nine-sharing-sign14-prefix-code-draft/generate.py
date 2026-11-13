#!/usr/bin/env python3
"""Generate source-only shared symbolic-code candidates from the pinned AST."""
import collections,hashlib,json
from pathlib import Path
here=Path(__file__).resolve().parent
src=here.parent/'nine-sharing-sign14-tau-candidate/seed.json';raw=src.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='7048a10d409ab5ff8031a444cd32117ba772b3834425c17a066188338e189ea9'
seed=json.loads(raw);counts=collections.Counter();sizes={}
def intern(t):
 x=tuple(t) if len(t)==2 else (t[0],intern(t[1]),intern(t[2]));counts[x]+=1;sizes[x]=1 if len(x)==2 else 1+sizes[x[1]]+sizes[x[2]];return x
roots=[intern(r['expr']) for r in seed['residuals']]
shared=sorted((x for x in counts if counts[x]>=2 and sizes[x]>=9),key=lambda x:(sizes[x],repr(x)));ids={x:i for i,x in enumerate(shared)};assert len(shared)==44
ports={'beta':0,'K0':1,'MC':2,'MF':3};numbers={1:'one',2:'two',3:'three',4:'four'}
def deps(x,self_id=None):
 found=set()
 def go(t):
  if t in ids and ids[t]!=self_id:found.add(ids[t]);return
  if len(t)==3:go(t[1]);go(t[2])
 go(x);return sorted(found)
def render(x,self_id=None):
 if x in ids and ids[x]!=self_id:return f'shared{ids[x]:02}'
 op=x[0]
 if op=='var':return f'Code.var {x[1]}'
 if op=='port':return f'Code.port {ports[x[1]]}'
 if op=='num':return f'Code.{numbers[x[1]]}'
 return f'(Code.{op} ({render(x[1])}) ({render(x[2])}))'
header='''/-! SOURCE-ONLY: generated shared code and interpretation candidates. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign14PrefixCode
open Sign14PrefixReflection
'''
for block in range(9):
 imp='Sign14PrefixReflection' if block==0 else f'Sign14PrefixCodeShared{block-1:02}'
 indices=list(range(block*5,min(block*5+5,44)));out=f'import DiophantineConsistency.{imp}\n\n'+header
 for i in indices:out+=f'def shared{i:02} : Code := {render(shared[i],i)}\n'
 out+='\nattribute [local irreducible] '+' '.join(f'shared{i:02}' for i in range(indices[-1]+1))+'\n\n'
 for i in indices:
  ds=deps(shared[i],i);out+=f'theorem shared{i:02}_interpret (p : Fin 4 → ℤ) :\n    interpret p shared{i:02} = SharingSeed14Degree124.shared{i:02} p := by\n  unfold shared{i:02}\n'
  rules=', '.join(['interpret']+[f'shared{j:02}_interpret' for j in ds]);out+=f'  simp only [{rules}] <;> rfl\n\n'
 out+='end DiophantineConsistency.Sign14PrefixCode\n'
 for i in indices:out+=f'#print axioms DiophantineConsistency.Sign14PrefixCode.shared{i:02}_interpret\n'
 (here/f'Sign14PrefixCodeShared{block:02}.lean').write_text(out)
for i,x in enumerate(roots):
 imp='Sign14PrefixCodeShared08' if i==0 else f'Sign14PrefixCodeRow{i-1:02}';out=f'import DiophantineConsistency.{imp}\n\n'+header
 out+=f'def row{i:02} : Code := {render(x)}\n\n'
 out+='attribute [local irreducible] '+' '.join(f'shared{j:02}' for j in range(44))+'\n\n'
 out+=f'theorem row{i:02}_interpret (p : Fin 4 → ℤ) :\n    interpret p row{i:02} = SharingSeed14Degree124.row{i:02} p := by\n  unfold row{i:02}\n'
 rules=', '.join(['interpret']+[f'shared{j:02}_interpret' for j in deps(x)]);out+=f'  simp only [{rules}] <;> rfl\n\nend DiophantineConsistency.Sign14PrefixCode\n'
 out+=f'#print axioms DiophantineConsistency.Sign14PrefixCode.row{i:02}_interpret\n'
 (here/f'Sign14PrefixCodeRow{i:02}.lean').write_text(out)
print(json.dumps({'status':'GENERATED_SOURCE_ONLY','shared':len(shared),'rows':len(roots)}))
