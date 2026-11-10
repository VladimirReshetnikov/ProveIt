#!/usr/bin/env python3
"""Generate source-only compositional degree bounds for staged sign14 AST."""
import collections,hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
here=Path(__file__).resolve().parent
src=here.parent/'nine-sharing-sign14-tau-candidate/seed.json';raw=src.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='7048a10d409ab5ff8031a444cd32117ba772b3834425c17a066188338e189ea9'
seed=json.loads(raw);counts=collections.Counter();sizes={}
def intern(t):
 x=tuple(t) if len(t)==2 else (t[0],intern(t[1]),intern(t[2]));counts[x]+=1;sizes[x]=1 if len(x)==2 else 1+sizes[x[1]]+sizes[x[2]];return x
roots=[intern(r['expr']) for r in seed['residuals']]
shared=sorted((x for x in counts if counts[x]>=2 and sizes[x]>=9),key=lambda x:(sizes[x],repr(x)));ids={x:i for i,x in enumerate(shared)};assert len(shared)==44
def degree(x):
 if len(x)==2:return int(x[0]=='var')
 a,b=degree(x[1]),degree(x[2]);return a+b if x[0]=='mul' else max(a,b)
def deps(x,self_id=None):
 found=set()
 def walk(t):
  if t in ids and ids[t]!=self_id:found.add(ids[t]);return
  if len(t)==3:walk(t[1]);walk(t[2])
 walk(x);return sorted(found)
assert [degree(x) for x in roots]==[22,22,2,62,46]
attrs=' '.join(f'shared{i:02}' for i in range(44))+' '+' '.join(f'row{i:02}' for i in range(5))
header='''/-! SOURCE-ONLY compositional degree bounds; not a full theorem. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14SyntaxDegree
open SharingSeed14Degree124
attribute [local irreducible] '''+attrs+'\n\n'
end='end DiophantineConsistency.Sign14SyntaxDegree\n'
def proof(label,x,self_id=None):
 d=degree(x); ds=deps(x,self_id);assert self_id is None or all(j<self_id for j in ds)
 lines=f'set_option maxHeartbeats 4000000 in\ntheorem {label}_degree (p : Fin 4 → ℤ) : degree ({label} p) ≤ {d} := by\n'
 for j in ds:lines+=f'  have h{j:02} := shared{j:02}_degree p\n'
 def form(t):
  if t in ids and ids[t]!=self_id:return f"degree (shared{ids[t]:02} p)"
  if len(t)==2:return '1' if t[0]=='var' else '0'
  left,right=form(t[1]),form(t[2])
  return f"({left} + {right})" if t[0]=='mul' else f"max ({left}) ({right})"
 lines+=f'  unfold {label}\n  change {form(x)} ≤ {d}\n  omega\n\n'
 return lines
for block in range(9):
 imp='Sign14SyntaxDegree' if block==0 else f'Sign14SharedDegree{block-1:02}'
 body=''.join(proof(f'shared{i:02}',shared[i],i) for i in range(block*5,min(block*5+5,44)))
 (here/f'Sign14SharedDegree{block:02}.lean').write_text(f'import DiophantineConsistency.{imp}\n\n'+header+body+end)
for i in range(5):
 imp='Sign14SharedDegree08' if i==0 else f'Sign14RowDegree{i-1:02}'
 body=proof(f'row{i:02}',roots[i])
 (here/f'Sign14RowDegree{i:02}.lean').write_text(f'import DiophantineConsistency.{imp}\n\n'+header+body+end)
print(json.dumps({'status':'GENERATED_SOURCE_ONLY','shared_degrees':[degree(x) for x in shared],
 'row_degrees':[degree(x) for x in roots],'scope':'source-only; no Lean or external binding claim'},sort_keys=True))
