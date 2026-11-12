#!/usr/bin/env python3
"""Generate one inert literal from the stable candidate; never invokes Lean."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1];path=D/'research/adaptive-square-sums38-two-quadratic-products/candidate.json';raw=path.read_bytes();assert hashlib.sha256(raw).hexdigest()=='ee523a8a821df163b038a19c4902234d3f09e730cbeee255dd4c896bdff7ae56';d=json.loads(raw)
assert len(d['witnesses'])==38 and len(d['source'])==160
ids=d['witnesses']+d['fixed_numerals']+[x[0] for x in d['source']];assert len(ids)==len(set(ids)) and all(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',x) for x in ids)
L=['import DiophantineConsistency.AdaptiveQM40Context','','/-! Source-only generated 38-variable literal. No Lean or model proof. -/','set_option autoImplicit false','set_option linter.unusedVariables false','set_option maxRecDepth 100000','noncomputable section','namespace DiophantineConsistency.AdaptiveQM38LiteralDraft','open AdaptiveEquationSyntax2011','','def literal (p : Fin 4 → ℤ) : Expr (Fin 38) :=']
L+=['  let '+n+' : Expr (Fin 38) := .var '+str(i) for i,n in enumerate(d['witnesses'])]
L+=['  let '+n+' : Expr (Fin 38) := .constant (p '+str(i)+')' for i,n in enumerate(d['fixed_numerals'])]
L+=['  -- BEGIN GENERATED ROWS']
L+=['  let '+n+' := '+str(a)+' '+op+' '+str(b) for n,op,a,b in d['source']]
L+=['  -- END GENERATED ROWS','  '+d['output'],'','end DiophantineConsistency.AdaptiveQM38LiteralDraft','']
(P/'AdaptiveQM38Literal.lean.src').write_text('\n'.join(L))
print(hashlib.sha256((P/'AdaptiveQM38Literal.lean.src').read_bytes()).hexdigest())
