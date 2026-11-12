#!/usr/bin/env python3
"""Generate inert exact 37-variable literal/residual sources; no Lean."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,(str(p),hashlib.sha256(b).hexdigest());return b.decode()
g=json.loads(pin(D/'research/adaptive-square-sums37-difference-quartic/candidate.json','b79e1a1fe708c7ba9a7406c8c534268d5b7e79128d8402c58637e16e5c462aea'))
old=pin(D/'research/adaptive-qm38-residual-evaluation-draft/AdaptiveQM38Residuals.lean.src','d0bb6ab27fbd9f70c5e4faf529a725ae065bf9787b570a8c675c38d21460fa97')
assert len(g['witnesses'])==37 and len(g['source'])==g['operations']==158
names=g['witnesses']+g['fixed_numerals']+[r[0] for r in g['source']];assert len(names)==len(set(names)) and all(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',x) for x in names)
L=['  let '+n+' : Expr (Fin 37) := .var '+str(i) for i,n in enumerate(g['witnesses'])]
L+=['  let '+n+' : Expr (Fin 37) := .constant (p '+str(i)+')' for i,n in enumerate(g['fixed_numerals'])]
L+=['  let '+n+' := '+str(a)+' '+op+' '+str(b) for n,op,a,b in g['source']]
body='\n'.join(L)
head='''import AdaptiveQM38Residuals

/-! Generated inert source: not Lean elaborated. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveQM37LiteralDraft
open AdaptiveEquationSyntax2011

def literal (p : Fin 4 → ℤ) : Expr (Fin 37) :=
'''
literal=head+body+'\n  '+g['output']+'\n\nend DiophantineConsistency.AdaptiveQM37LiteralDraft\n'
(P/'AdaptiveQM37Literal.lean.src').write_text(literal)
oldres=re.findall(r'^  !\[([^\n]+)\]$',old,re.M);assert len(oldres)==1
parent=oldres[0].split(',');assert len(parent)==29 and parent[4]=='squareDifference' and parent[21]=='ySquareDifference'
res=[('differenceEquality' if i==4 else n) for i,n in enumerate(parent) if i!=21];assert len(res)==28
node={x:('leaf',x) for x in g['witnesses']+g['fixed_numerals']}
def v(x):return ('constant',x) if type(x)==int else node[x]
for n,o,a,b in g['source']:node[n]=(o,v(a),v(b))
s=None
for n in res:
 sq=('*',node[n],node[n]);s=sq if s is None else ('+',s,sq)
assert s==node[g['output']]
reshead='''import AdaptiveQM37Literal

/-! Generated inert residual vector; no Lean elaboration. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option Elab.async false
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveQM37ResidualsDraft
open AdaptiveEquationSyntax2011

def residuals (p : Fin 4 → ℤ) : Fin 28 → Expr (Fin 37) :=
'''
sumexpr=' + '.join(f'(residuals p {i})*(residuals p {i})' for i in range(28))
resfile=reshead+body+'\n  !['+','.join(res)+']\n\ndef sum (p : Fin 4 → ℤ) : Expr (Fin 37) := '+sumexpr+'''\n\ntheorem sum_eq_literal (p : Fin 4 → ℤ) : sum p = AdaptiveQM37LiteralDraft.literal p := by rfl
end DiophantineConsistency.AdaptiveQM37ResidualsDraft
#print axioms DiophantineConsistency.AdaptiveQM37ResidualsDraft.sum_eq_literal
'''
(P/'AdaptiveQM37Residuals.lean.src').write_text(resfile)
print(json.dumps({'scope':'source-only generated literal and exact structural square sum; no Lean','positive_variables':37,'rows':158,'residuals':28,'parent_residuals':29,'square_sum_exact_DAG':True,'literal_sha256':hashlib.sha256(literal.encode()).hexdigest(),'residual_source_sha256':hashlib.sha256(resfile.encode()).hexdigest()},indent=2,sort_keys=True))
