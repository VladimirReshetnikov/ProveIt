from pathlib import Path
from hashlib import sha256
import json,re
D=Path('research/ordinary13-positive84-to87-unscale-model-draft')
for label,path,expected in [('84','research/ordinary13-qcube-unscale84/candidate.json',84),('87','research/ordinary13-aux-root87-36/candidate.json',87)]:
 p=Path(path);g=json.loads(p.read_text());assert len(g['source'])==expected
 names=g['witnesses']+g['fixed_numerals']+[r[0] for r in g['source']]
 assert len(names)==len(set(names)) and all(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',n) for n in names)
 lines=['  let '+n+' : Expr (Fin 13) := .var '+str(i) for i,n in enumerate(g['witnesses'])]
 lines+=['  let '+n+' : Expr (Fin 13) := .constant (p '+str(i)+')' for i,n in enumerate(g['fixed_numerals'])]
 lines+=['  let '+n+' := '+str(a)+' '+op+' '+str(b) for n,op,a,b in g['source']]
 src='''import DiophantineConsistency.AdaptiveEquationSyntax2011

/-! Generated exact JSON literal; source only, not elaborated. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 100000
noncomputable section
namespace PositiveUnscale'''+label+'''GraphDraft
open DiophantineConsistency.AdaptiveEquationSyntax2011
structure Graph where
  first : Expr (Fin 13)
  main : Expr (Fin 13)
  aux : Expr (Fin 13)
  strong : Expr (Fin 13)
  root : Expr (Fin 13)
  bt : Expr (Fin 13)
  ell : Expr (Fin 13)
  k : Expr (Fin 13)
  output : Expr (Fin 13)
def graph (p : Fin 4 → ℤ) : Graph :=
'''+ '\n'.join(lines)+'\n  ⟨A0,A1,Fa,g72,Z,Bt,ell,k,out⟩\nend PositiveUnscale'+label+'GraphDraft\n'
 (D/('PositiveUnscale'+label+'Graph.lean.src')).write_text(src)
