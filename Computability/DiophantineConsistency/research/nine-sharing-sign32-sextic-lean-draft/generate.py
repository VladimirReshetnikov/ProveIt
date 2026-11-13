#!/usr/bin/env python3
"""Generate bounded source-only Lean syntax from the pinned sign32 sextic residual AST."""
import hashlib, json, sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1]
source=D/'research/nine-sharing-sign32-sextic-candidate-v2/seed.json'
b=source.read_bytes(); assert hashlib.sha256(b).hexdigest()=='f26172a2cad6e6a8fda042c67821f2fa7651426a62e980173eb5fac07cd835ab'
d=json.loads(b); assert d['witness_count']==32 and d['total_coordinates']==33 and len(d['residuals'])==23
ports={'beta':0,'K0':1,'MC':2,'MF':3};count=0
def render(t,depth=0):
    global count
    count+=1;assert count<=100000 and depth<=80 and isinstance(t,list) and t
    k=t[0]
    if k=='num':
        assert len(t)==2 and type(t[1]) is int and 0<=t[1]<=10
        return f'(Expr.constant ({t[1]} : ℤ))',0
    if k=='port':
        assert len(t)==2 and t[1] in ports
        return f'(Expr.constant (p {ports[t[1]]}))',0
    if k=='var':
        assert len(t)==2 and type(t[1]) is int and 1<=t[1]<=32
        return f'(Expr.var {t[1]})',1
    assert len(t)==3 and k in ('add','sub','mul')
    a,da=render(t[1],depth+1);b,db=render(t[2],depth+1)
    symbol={'add':'+','sub':'-','mul':'*'}[k]
    return f'({a} {symbol} {b})', da+db if k=='mul' else max(da,db)
terms=[]
for residual in d['residuals']:
    term,degree=render(residual['expr']);assert degree<=3;terms.append(term)
header='''import DiophantineConsistency.NineFreshJones

/-! UNCOMPILED generated syntax only. External JSON binding is separately
checked; no all-model bridge or iPRA endpoint is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed32Sextic

/-- The first residual; all witness-zero values make it `-(p 0 + 1)^3`. -/
def firstResidual (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  '''+terms[0]+'''

/-- The remaining 22 residuals, in the external candidate order. -/
def remainingResiduals (p : Fin 4 → ℤ) : List (Expr (Fin 33)) :=
  [
'''
footer='''
  ]

/-- Sum of the 23 squared residuals; coordinate 0 is unused. -/
def seed (p : Fin 4 → ℤ) : Expr (Fin 33) :=
  firstResidual p * firstResidual p +
    QuarticSyntax.sumExpressions ((remainingResiduals p).map fun e => e * e)

/-- Keep the distinguished input arbitrary and set all 32 witnesses to zero. -/
def zeroWitness (x : ℤ) (j : Fin 33) : ℤ := if j = 0 then x else 0

end DiophantineConsistency.SharingSeed32Sextic
'''
out=header+',\n'.join('    '+t for t in terms[1:])+footer
target=P/'SharingSeed32Sextic.lean';assert not target.exists();target.write_text(out)
print(json.dumps({'status':'GENERATED_SOURCE_ONLY','source_sha256':hashlib.sha256(out.encode()).hexdigest(),'seed_json_sha256':hashlib.sha256(b).hexdigest(),'residuals':len(terms),'ast_nodes':count,'scope':'Generated syntax only; no Lean check or model bridge.'},indent=2,sort_keys=True))
