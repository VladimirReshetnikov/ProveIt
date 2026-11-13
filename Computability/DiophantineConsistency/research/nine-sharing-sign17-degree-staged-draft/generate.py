#!/usr/bin/env python3
"""Generate source-only compositional degree bounds for staged sign17 AST."""
import collections,hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
here=Path(__file__).resolve().parent
src=here.parent/'nine-sharing-sign17-degree96-vdifference-candidate/seed.json';raw=src.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='0323ee371aac07604617495952c6a5e0b7ead5e66697a485a05358fb447689ac'
seed=json.loads(raw);counts=collections.Counter();sizes={}
def intern(t):
 x=tuple(t) if len(t)==2 else (t[0],intern(t[1]),intern(t[2]));counts[x]+=1;sizes[x]=1 if len(x)==2 else 1+sizes[x[1]]+sizes[x[2]];return x
roots=[intern(r['expr']) for r in seed['residuals']]
shared=sorted((x for x in counts if counts[x]>=2 and sizes[x]>=9),key=lambda x:(sizes[x],repr(x)));ids={x:i for i,x in enumerate(shared)};assert len(shared)==35
def degree(x):
 if len(x)==2:return int(x[0]=='var')
 a,b=degree(x[1]),degree(x[2]);return a+b if x[0]=='mul' else max(a,b)
def deps(x,self_id=None):
 found=set()
 def walk(t):
  if t in ids and ids[t]!=self_id:found.add(ids[t]);return
  if len(t)==3:walk(t[1]);walk(t[2])
 walk(x);return sorted(found)
assert [degree(x) for x in roots]==[22,7,22,2,6,5,48,46]
attrs=' '.join(f'shared{i:02}' for i in range(35))+' '+' '.join(f'row{i:02}' for i in range(8))
header='''/-! SOURCE-ONLY compositional degree bounds; not a full theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17SyntaxDegree
open SharingSeed17Degree96
attribute [local irreducible] '''+attrs+'\n\n'
end='end DiophantineConsistency.Sign17SyntaxDegree\n'
def proof(label,x,self_id=None):
 d=degree(x); ds=deps(x,self_id);assert self_id is None or all(j<self_id for j in ds)
 lines=f'set_option maxHeartbeats 4000000 in\ntheorem {label}_degree (p : Fin 4 → ℤ) : degree ({label} p) ≤ {d} := by\n'
 for j in ds:lines+=f'  have h{j:02} := shared{j:02}_degree p\n'
 lines+=f'  unfold {label}\n  first\n  | change {d} ≤ {d}; decide\n  | simp only [degree]; omega\n\n'
 return lines
for block in range(1,7):
 imp='Sign17SharedDegree00' if block==1 else f'Sign17SharedDegree{block-1:02}'
 body=''.join(proof(f'shared{i:02}',shared[i],i) for i in range(block*5,block*5+5))
 (here/f'Sign17SharedDegree{block:02}.lean').write_text(f'import DiophantineConsistency.{imp}\n\n'+header+body+end)
for block in range(2):
 imp='Sign17SharedDegree06' if block==0 else 'Sign17RowDegrees00'
 body=''.join(proof(f'row{i:02}',roots[i]) for i in range(block*4,block*4+4))
 (here/f'Sign17RowDegrees{block:02}.lean').write_text(f'import DiophantineConsistency.{imp}\n\n'+header+body+end)
print(json.dumps({'status':'GENERATED_SOURCE_ONLY','shared_degrees':[degree(x) for x in shared],
 'row_degrees':[degree(x) for x in roots],'scope':'source-only; no Lean or external binding claim'},sort_keys=True))
