#!/usr/bin/env python3
"""Generate exact literal fields from the pinned structural prototype."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
here=Path(__file__).resolve().parent;root=here.parents[1]
b=(root/'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json').read_bytes()
pin='97273735d1537b597544604d19969630c8464469e9a3ab2f8825f52dc602a648'
assert hashlib.sha256(b).hexdigest()==pin
g=json.loads(b); assert len(g['witnesses'])==13
names=g['witnesses']+g['fixed_numerals']+[r[0] for r in g['source']]
assert len(names)==len(set(names)) and all(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',n) for n in names)
body='\n'.join(['  let '+n+' : Expr (Fin 13) := .var '+str(i) for i,n in enumerate(g['witnesses'])]+['  let '+n+' : Expr (Fin 13) := .constant (p '+str(i)+')' for i,n in enumerate(g['fixed_numerals'])]+['  let '+n+' := '+str(a)+' '+op+' '+str(c) for n,op,a,c in g['source']])
fields=['first','main','aux','strong','output','strongResidual','b','z','x','s','k','u','a','c','d','y','vv','f','ii','ell','delta']
vals=['A0','A1','Fa','Fs','out','g72','qm','Z','X','s','k','U','a','c','Dstar','n_y','V','n_f','I','ell','Delta']
head='''import DiophantineConsistency.AdaptiveEquationSyntax2011

/-! Generated prototype syntax; all model theorems remain source drafts. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 100000
noncomputable section
namespace EtaNaturalUnitGraphDraft
open DiophantineConsistency.AdaptiveEquationSyntax2011

structure Graph where
'''
out=head+''.join('  '+x+' : Expr (Fin 13)\n' for x in fields)+'\ndef graph (p : Fin 4 → ℤ) : Graph :=\n'+body+'\n  ⟨'+', '.join(vals)+'⟩\n\nend EtaNaturalUnitGraphDraft\n'
p=here/'EtaNaturalUnitGraph.lean.src';by=out.encode()
if '--write' in sys.argv:p.write_bytes(by)
else:assert p.read_bytes()==by
print(json.dumps({'prototype_sha256':pin,'literal_sha256':hashlib.sha256(by).hexdigest(),'fields':dict(zip(fields,vals)),'scope':'graph source generation only; no Lean'},sort_keys=True,indent=2))
