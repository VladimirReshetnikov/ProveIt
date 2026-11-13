from pathlib import Path
import json,hashlib,re
p=Path('research/ordinary13-positive80-to81-model-draft')
f=Path('research/ordinary13-residue-first81/candidate.json');b=f.read_bytes()
assert hashlib.sha256(b).hexdigest()=='067d3cf0e92961d272e9018dde38bbe8b00ad55ec8e9145fbdd34c0f13e18352'
g=json.loads(b);assert len(g['source'])==81 and len(g['witnesses'])==13
names=g['witnesses']+g['fixed_numerals']+[r[0] for r in g['source']]
assert len(names)==len(set(names)) and all(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',n) for n in names)
lines=['  let '+n+' : Expr (Fin 13) := .var '+str(i) for i,n in enumerate(g['witnesses'])]
lines+=['  let '+n+' : Expr (Fin 13) := .constant (p '+str(i)+')' for i,n in enumerate(g['fixed_numerals'])]
lines+=['  let '+n+' := '+str(a)+' '+op+' '+str(c) for n,op,a,c in g['source']]
out='''import DiophantineConsistency.AdaptiveEquationSyntax2011

/-! Exact positive 81 four-square graph; generated, unelaborated source. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 100000
noncomputable section
namespace PositiveSquare81GraphDraft
open DiophantineConsistency.AdaptiveEquationSyntax2011
structure Graph where
  first : Expr (Fin 13)
  main : Expr (Fin 13)
  aux : Expr (Fin 13)
  strongResidual : Expr (Fin 13)
  output : Expr (Fin 13)

def graph (p : Fin 4 → ℤ) : Graph :=
'''+ '\n'.join(lines)+'\n  ⟨A0,A1,Fa,g72,out⟩\nend PositiveSquare81GraphDraft\n'
(p/'PositiveSquare81Graph.lean.src').write_text(out)
