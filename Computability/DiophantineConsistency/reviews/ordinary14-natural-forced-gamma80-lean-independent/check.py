#!/usr/bin/env python3
"""Reconstruct the proposed source from the pinned graph; does not run Lean."""
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parents[2]
def pin(path,digest):
 b=(D/path).read_bytes();assert hashlib.sha256(b).hexdigest()==digest,path;return b
candidate=pin('research/ordinary14-natural-forced-gamma80/candidate.json','136560324b95b3fda68d10ebe49bdba0a02e950e0bf6b7f1b1588baea4805bf5')
lean=pin('research/ordinary14-natural-forced-gamma80-lean-draft/P80NaturalForcedGamma.lean','015214c4176ab1600c573297521b43987eb66fe863d918a6bcff803a76ca44d9')
g=json.loads(candidate); inputs=g['witnesses'];ports=g['fixed_numerals'];rows=g['source']
assert g['domain']=='nonnegative integers' and g['output']=='out' and g['operations']==len(rows)==80
assert inputs==['n_J','n_F','n_alpha','n_f','n_i','n_T','n_w','n_s','n_r','n_eta','n_zeta','n_y','n_gamma','n_h']
assert ports==['beta','K0','MC','MF']
fields=['first','main','aux','strong','guardFactor','output','qF','C','G','rank']
nodes=['F0','F1','Fa','Fs','guard','out','qF','C','G','R']
seen=set(inputs+ports); assert len(seen)==18
for n,op,x,y in rows:
 assert n not in seen and op in ('+','-','*')
 assert all(type(a) is int or a in seen for a in (x,y));seen.add(n)
live={'out'}
for n,op,x,y in reversed(rows):
 if n in live:live.update(a for a in (x,y) if isinstance(a,str))
assert set(inputs+ports)|{r[0] for r in rows} <= live
by={n:[op,x,y] for n,op,x,y in rows}
assert by['P01']==['*','F0','F1'] and by['P012']==['*','P01','Fa']
assert by['P0123']==['*','P012','Fs'] and by['P01234']==['*','P0123','guard']
assert by['out']==['-','P01234',1]
header='''import DiophantineConsistency.AdaptiveEquationSyntax2011

/-! Literal source-only proposal. No Lean elaboration or endpoint claim. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace P80NaturalForcedGamma
open DiophantineConsistency AdaptiveEquationSyntax2011

structure Graph where
'''
source=header+''.join(f'  {n} : Expr (Fin 14)\n' for n in fields)
source+='''
set_option linter.unusedVariables false in
def graph (p : Fin 4 → ℤ) : Graph :=
'''
source+=''.join(f'  let {n} : Expr (Fin 14) := .var {i}\n' for i,n in enumerate(inputs))
source+=''.join(f'  let {n} : Expr (Fin 14) := .constant (p {i})\n' for i,n in enumerate(ports))
source+='  -- BEGIN LITERAL GRAPH\n'
source+=''.join(f'  let {n} := {x} {op} {y}\n' for n,op,x,y in rows)
source+='  -- END LITERAL GRAPH\n  ⟨'+', '.join(nodes)+'⟩\n'
source+='''
theorem output_shape (p : Fin 4 → ℤ) : (graph p).output =
    (graph p).first * (graph p).main * (graph p).aux *
      (graph p).strong * (graph p).guardFactor - 1 := by rfl

end P80NaturalForcedGamma

#print axioms P80NaturalForcedGamma.output_shape
'''
assert source.encode()==lean
print(json.dumps({'scope':'independent byte-for-byte source reconstruction, not Lean elaboration or semantic theorem',
 'inputs':len(inputs),'ports':len(ports),'gates':len(rows),'fields':dict(zip(fields,nodes)),
 'all_gates_inputs_ports_live':True,'output_product_shape_checked':True},sort_keys=True,indent=2))
