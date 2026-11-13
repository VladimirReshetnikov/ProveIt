#!/usr/bin/env python3
"""Render/verify reviewed literal graphs. Never invokes Lean."""
from pathlib import Path
import hashlib,json,sys
P=Path(__file__).resolve().parent;D=P.parents[1]
SPECS=[('ordinary14-negative-pell75','P75NegativePell',75,'89a9a0217d28d655fbf2592d995f4d766175a45560fa4d33b251dd3711e5b1c1','Fg'),('ordinary14-positive-guard74','P74PositiveGuard',74,'e70af4f896013695368180743f514c027faa86f8b3cedd5479b22e64e4c26093','guard')]
witness=['J','F','alpha','f','i','T','w','s','r','eta','zeta','y','gamma','h'];ports=['beta','K0','MC','MF']
fields=[('first','F0'),('main','F1'),('aux','Fa'),('strong','Fs'),('guardFactor',None),('output','out'),('b','qm'),('q','q'),('X','X'),('Y','Y'),('k','k'),('ell','ell'),('a','a'),('c','c'),('U','U'),('Dstar','Dstar'),('Q','Q'),('I','I'),('vroot','V'),('C','C')]
if sys.argv[1:] not in ([],['--check']):raise SystemExit('usage: make_graph.py [--check]')
results=[]
for directory,namespace,count,expected,guard in SPECS:
 raw=(D/'research'/directory/'candidate.json').read_bytes();assert hashlib.sha256(raw).hexdigest()==expected
 g=json.loads(raw);assert g['witnesses']==witness and g['fixed_numerals']==ports and len(g['source'])==count and g['operations']==count and g['output']=='out'
 head=f'''import DiophantineConsistency.AdaptiveEquationSyntax2011

/-! Literal source-only proposal. No Lean elaboration, binding or endpoint claimed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace {namespace}
open DiophantineConsistency AdaptiveEquationSyntax2011

structure Graph where
'''
 head+=''.join('  '+name+' : Expr (Fin 14)\n' for name,_ in fields)
 head+='''
set_option linter.unusedVariables false in
def graph (p : Fin 4 → ℤ) : Graph :=
'''
 lines=[f'  let {n} : Expr (Fin 14) := .var {i}' for i,n in enumerate(witness)]
 lines += [f'  let {n} : Expr (Fin 14) := .constant (p {i})' for i,n in enumerate(ports)]
 lines += ['  -- BEGIN LITERAL GRAPH'];available=set(witness+ports);seen=set()
 for row in g['source']:
  assert len(row)==4
  n,op,a,b=row
  assert n not in available and n not in seen and op in ('+','-','*'),row
  for x in (a,b):assert type(x) is int or x in available,(n,x)
  lines.append(f'  let {n} := {a} {op} {b}');available.add(n);seen.add(n)
 assert all((guard if node is None else node) in available for _,node in fields)
 lines+=['  -- END LITERAL GRAPH','  ⟨'+', '.join(guard if node is None else node for _,node in fields)+'⟩']
 tail=f'''

theorem output_shape (p : Fin 4 → ℤ) : (graph p).output =
    (graph p).first * (graph p).main * (graph p).aux *
      (graph p).strong * (graph p).guardFactor - 1 := by rfl

end {namespace}

#print axioms {namespace}.output_shape
'''
 data=(head+'\n'.join(lines)+tail).encode();out=P/(namespace+'.lean')
 if sys.argv[1:]==['--check']:assert out.read_bytes()==data
 else:
  assert not out.exists(),('refusing to overwrite',str(out));out.write_bytes(data)
 results.append({'candidate':directory+'/candidate.json','candidate_sha256':expected,'literal_source':out.name,'source_sha256':hashlib.sha256(data).hexdigest(),'operation_rows':count,'field_nodes':{name:(guard if node is None else node) for name,node in fields},'witnesses':witness,'fixed_numerals':ports})
print(json.dumps({'scope':'source generation only, no Lean elaboration or graph theorem','graphs':results},sort_keys=True,indent=2))
