#!/usr/bin/env python3
"""Generate small staged Lean Expr definitions from pinned positive AST; no Lean proof."""
import collections,hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;source=P.parent/'nine-sharing-sign14-positive74-candidate/seed.json';raw=source.read_bytes();pinned=hashlib.sha256(raw).hexdigest();data=json.loads(raw)
expected=json.loads((P.parent/'nine-sharing-sign14-positive74-candidate/result.json').read_text())['candidate_sha256']
if pinned!=expected:raise RuntimeError('candidate pin')
nodes=[];ids={}
def node(op,a,b):
 k=(op,a,b)
 if k not in ids:ids[k]=len(nodes);nodes.append(k)
 return ('node',ids[k])
def lower(e):
 if e[0] in ('add','sub','mul'):return node(e[0],lower(e[1]),lower(e[2]))
 if e[0] in ('var','port','num'):return tuple(e)
 raise ValueError(e[0])
roots=[lower(row['expr']) for row in data['residuals']]
if len(nodes)!=65:raise RuntimeError('unexpected residual gate count')
ports={'beta':0,'K0':1,'MC':2,'MF':3}
def term(x):
 typ,val=x
 if typ=='node':return f'(g{val:02d} p)'
 if typ=='port':return f'(Expr.constant (p {ports[val]}))'
 if typ=='var':
  if not 1<=val<=14:raise ValueError('variable')
  return f'(Expr.var {val-1})'
 if typ=='num':return f'(Expr.constant {val})'
 raise ValueError(typ)
for stage in range(9):
 first=stage*8;last=min(first+8,len(nodes));imp='Sign14Optimized86Expression' if stage==0 else f'Sign14Positive74Nodes{stage-1:02d}'
 lines=[f'import DiophantineConsistency.{imp}','','/-! Source-only generated positive-coordinate circuit nodes. -/','set_option autoImplicit false','noncomputable section','namespace DiophantineConsistency.Sign14Positive74','']
 for i in range(first,last):
  op,a,b=nodes[i];symbol={'add':'+','sub':'-','mul':'*'}[op];lines.append(f'def g{i:02d} (p : Fin 4 → ℤ) : Expr (Fin 14) := {term(a)} {symbol} {term(b)}')
 lines+=['','end DiophantineConsistency.Sign14Positive74',''];(P/f'Sign14Positive74Nodes{stage:02d}.lean').write_text('\n'.join(lines))
lines=['import DiophantineConsistency.Sign14Positive74Nodes08','','/-! Source-only positive-coordinate candidate, sum of five squares. -/','set_option autoImplicit false','noncomputable section','namespace DiophantineConsistency.Sign14Positive74','']
for i,x in enumerate(roots):lines.append(f'def row{i:02d} (p : Fin 4 → ℤ) : Expr (Fin 14) := {term(x)}')
lines+=['','def expression (p : Fin 4 → ℤ) : Expr (Fin 14) :=', '  row00 p * row00 p + row01 p * row01 p + row02 p * row02 p +', '    row03 p * row03 p + row04 p * row04 p','','end DiophantineConsistency.Sign14Positive74',''];(P/'Sign14Positive74Expression.lean').write_text('\n'.join(lines))
print(json.dumps({'status':'SOURCE_ONLY','candidate_sha256':pinned,'residual_nodes':len(nodes),'stages':10,'root_nodes':[v for k,v in roots]},sort_keys=True))
