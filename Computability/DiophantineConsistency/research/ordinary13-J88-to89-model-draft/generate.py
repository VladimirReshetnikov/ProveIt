from pathlib import Path
import json,hashlib,re
p=Path('research/ordinary13-J88-to89-model-draft')
f=Path('research/ordinary13-natural-unit-product89/candidate.json')
b=f.read_bytes();assert hashlib.sha256(b).hexdigest()=='1d865512c2c78580af0d6a5285c009e5fa03deb141dc711dc5e3adb0b268938d'
g=json.loads(b);assert len(g['source'])==89 and len(g['witnesses'])==13 and len(g['fixed_numerals'])==4
names=g['witnesses']+g['fixed_numerals']+[r[0] for r in g['source']]
assert len(names)==len(set(names)) and all(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',n) for n in names)
lines=['  let '+n+' : Expr (Fin 13) := .var '+str(i) for i,n in enumerate(g['witnesses'])]
lines+=['  let '+n+' : Expr (Fin 13) := .constant (p '+str(i)+')' for i,n in enumerate(g['fixed_numerals'])]
lines+=['  let '+n+' := '+str(a)+' '+op+' '+str(c) for n,op,a,c in g['source']]
out='''import DiophantineConsistency.AdaptiveEquationSyntax2011

/-! Exact generated 89-operation natural parent; unelaborated source. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 100000
noncomputable section
namespace JShifted89GraphDraft
open DiophantineConsistency.AdaptiveEquationSyntax2011

def literal (p : Fin 4 → ℤ) : Expr (Fin 13) :=
'''+ '\n'.join(lines)+'\n  '+g['output']+'\nend JShifted89GraphDraft\n'
(p/'JShifted89Graph.lean.src').write_text(out)
