#!/usr/bin/env python3
"""Generate source-only staged sign15 expression syntax with shared subtrees."""
import hashlib,json,sys
from collections import Counter
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
here=Path(__file__).resolve().parent;src=here.parent/'nine-sharing-sign15-inner-candidate/seed.json';raw=src.read_bytes();assert hashlib.sha256(raw).hexdigest()=='bdd841f25618a01e659d6f2f802f0420501b00c5270df9fa56b9589733ecbd59';d=json.loads(raw);assert d['witness_count']==15 and len(d['residuals'])==6
counts=Counter();sizes={}
def intern(t):
 x=tuple(t) if len(t)==2 else (t[0],intern(t[1]),intern(t[2]));counts[x]+=1;sizes[x]=1 if len(x)==2 else 1+sizes[x[1]]+sizes[x[2]];return x
roots=[intern(r['expr']) for r in d['residuals']];shared=sorted((x for x in counts if counts[x]>=2 and sizes[x]>=9),key=lambda x:(sizes[x],repr(x)));ids={x:i for i,x in enumerate(shared)};assert len(shared)==40
ports={'beta':0,'K0':1,'MC':2,'MF':3}
def render(x,self_id=None):
 if x in ids and ids[x]!=self_id:return f'(shared{ids[x]:02} p)'
 if x[0]=='num':return f'(Expr.constant ({x[1]} : ℤ))'
 if x[0]=='port':return f'(Expr.constant (p {ports[x[1]]}))'
 if x[0]=='var':return f'(Expr.var {x[1]})'
 op={'add':'+','sub':'-','mul':'*'}[x[0]];return f'({render(x[1])} {op} {render(x[2])})'
def write(n,text):
 p=here/n
 if p.exists():raise SystemExit('refusing overwrite '+n)
 p.write_text(text)
header='set_option autoImplicit false\nset_option maxHeartbeats 4000000\nnoncomputable section\nnamespace DiophantineConsistency.SharingSeed15Degree124\n';end='end DiophantineConsistency.SharingSeed15Degree124\n'
for block in range(8):
 imp='DiophantineConsistency.NineFreshJones' if block==0 else f'DiophantineConsistency.SharingSeed15Shared{block-1:02}'
 body=''.join(f'def shared{i:02} (p : Fin 4 → ℤ) : Expr (Fin 16) :=\n  {render(shared[i],i)}\n' for i in range(block*5,min(block*5+5,len(shared))))
 write(f'SharingSeed15Shared{block:02}.lean',f'import {imp}\n\n/-! SOURCE-ONLY staged shared syntax. -/\n'+header+body+end)
for i,x in enumerate(roots):
 write(f'SharingSeed15Row{i:02}.lean',f'import DiophantineConsistency.SharingSeed15Shared07\n\n/-! SOURCE-ONLY staged residual. -/\n'+header+f'def row{i:02} (p : Fin 4 → ℤ) : Expr (Fin 16) :=\n  {render(x)}\n'+end)
imports='\n'.join(f'import DiophantineConsistency.SharingSeed15Row{i:02}' for i in range(6));items=', '.join(f'row{i:02} p' for i in range(1,6))
write('SharingSeed15Degree124.lean',imports+'\n\n/-! SOURCE-ONLY staged seed assembly. -/\n'+header+f'''def firstResidual (p : Fin 4 → ℤ) : Expr (Fin 16) := row00 p\ndef remainingResiduals (p : Fin 4 → ℤ) : List (Expr (Fin 16)) := [{items}]\ndef seed (p : Fin 4 → ℤ) : Expr (Fin 16) :=\n  firstResidual p * firstResidual p +\n    QuarticSyntax.sumExpressions ((remainingResiduals p).map fun e => e * e)\ndef zeroWitness (x : ℤ) (j : Fin 16) : ℤ := if j = 0 then x else 0\n'''+end)
old=here.parent/'nine-sharing-sign19-model-bridge-draft/SharingSign19Squares.lean';write('SharingSign15Squares.lean',old.read_text().replace('SharingSeed19Degree44','SharingSeed15Degree124').replace('SharingSign19Squares','SharingSign15Squares').replace('sign19','sign15').replace('Fin 20','Fin 16'))
print(json.dumps({'status':'GENERATED_SOURCE_ONLY','shared_subtrees':len(shared),'shared_modules':8,'residual_modules':6,'seed_sha256':hashlib.sha256(raw).hexdigest(),'scope':'Uncompiled; no Lean bridge or endpoint.'},sort_keys=True,indent=2))
