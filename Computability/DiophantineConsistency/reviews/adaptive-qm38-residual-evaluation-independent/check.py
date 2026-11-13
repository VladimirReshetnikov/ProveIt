#!/usr/bin/env python3
"""Independent residual-index and source-composition review; no Lean."""
from pathlib import Path
import hashlib,json,re,sys
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('Use python3 -I -S -B')
D=Path(__file__).resolve().parents[2]
files={
'child':('research/adaptive-square-sums38-two-quadratic-products/candidate.json','ee523a8a821df163b038a19c4902234d3f09e730cbeee255dd4c896bdff7ae56'),
'parent':('Lean/DiophantineConsistency/AdaptiveQM40Context.lean','be48ed96bcb082715c99cd697bfa25ff21bd55aa789e868970b74e621422dece'),
'child_literal':('research/adaptive-qm38-conditional-model-draft/AdaptiveQM38Literal.lean.src','f033af128e5ca4c7a5a1473e6370fc385d0354b110067ae84e168eed6643a44d'),
'cut':('research/adaptive-qm38-conditional-model-draft/AdaptiveQM38EvaluationCut.lean.src','08707aa597d45389ab038fcda534d342ec4487913da52832ea441241fa9fee0b'),
'residuals':('research/adaptive-qm38-residual-evaluation-draft/AdaptiveQM38Residuals.lean.src','d0bb6ab27fbd9f70c5e4faf529a725ae065bf9787b570a8c675c38d21460fa97'),
'proof':('research/adaptive-qm38-residual-evaluation-draft/AdaptiveQM38ResidualEvaluation.lean.src','338fdf383779b3b9e155b0982700f609092b0e70109fc6c28482abefebd231ad'),
'author_result':('research/adaptive-qm38-residual-evaluation-draft/source-result.json','fe6c8a92d33aa9350f6a215b43c7a576593ed2f2ebbb8bad4a24a443194e39a4'),
'external_graph_review':('reviews/adaptive-square-sums38-independent/result.json','5173a65bc0dd0140de5995e014929ad00fb05c0446b3367222ce8b6e6743aaff'),
'conditional_review':('reviews/adaptive-qm38-conditional-model-independent/result.json','b12b08d2ae0abe95802eed95e1967537dfe1ca7d97f5a8bd7c0a8c19a3eeb2b4')}
s={}
for n,(p,h) in files.items():
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,n;s[n]=b.decode()
g=json.loads(s['child']);parent=s['parent'];res=s['residuals'];proof=s['proof']
old=parent.split('def residuals (p : Fin 4 → ℤ) : Fin 31 → Expr (Fin 40) :=',1)[1].split('\ndef sum ',1)[0]
m=re.search(r'  !\[([^\n]+)\]',old);assert m;oldnames=m[1].split(',');assert len(oldnames)==31
assert oldnames[20]=='ellProductDifference' and oldnames[24]=='deltaProductDifference'
keep=[(i,n) for i,n in enumerate(oldnames) if i not in (20,24)]
block=res.split('def residuals (p : Fin 4 → ℤ) : Fin 29 → Expr (Fin 38) :=\n',1)[1].split('\n\ndef sum ',1)[0]
expected=[f'  let {n} : Expr (Fin 38) := .var {i}' for i,n in enumerate(g['witnesses'])]
expected += [f'  let {n} : Expr (Fin 38) := .constant (p {i})' for i,n in enumerate(g['fixed_numerals'])]
expected += [f'  let {n} := {x} {op} {y}' for n,op,x,y in g['source']]
expected += ['  !['+','.join(n for _,n in keep)+']']
assert block.splitlines()==expected
# Evaluate the output as a formal expression DAG and compare to ordered sum.
env={n:('leaf',n) for n in g['witnesses']+g['fixed_numerals']}
def get(x):return ('const',x) if type(x)==int else env[x]
for n,o,x,y in g['source']:env[n]=(o,get(x),get(y))
terms=[('*',env[n],env[n]) for _,n in keep];fold=terms[0]
for x in terms[1:]:fold=('+',fold,x)
assert env[g['output']]==fold
assert 'theorem sum_eq_literal (p : Fin 4 → ℤ) : sum p = AdaptiveQM38LiteralDraft.literal p := by rfl' in res
# Match each individual theorem block to its exact parent and child indices.
for j,(i,n) in enumerate(keep):
 start=proof.index(f'theorem residual{j:02d} (');end=proof.find('\n/--',start)
 block=proof[start:end]
 assert f'(AdaptiveQM40Context.residuals p {i}).evalRing (fun k => ι (extend v k))' in block
 assert f'(AdaptiveQM38ResidualsDraft.residuals p {j}).evalRing (fun k => ι (v k))' in block
 assert 'simp [AdaptiveQM40Context.residuals, AdaptiveQM38ResidualsDraft.residuals,' in block and '<;> ring' in block
for i in (20,24):
 start=proof.index(f'theorem dropped{i} (');end=proof.find('\n/--',start);block=proof[start:end]
 assert f'(AdaptiveQM40Context.residuals p {i}).evalRing (fun k => ι (extend v k)) = 0' in block
 assert '<;> ring' in block
start=proof.index('theorem evaluation_identity (');end=proof.index('\ntheorem evaluation_cut',start);whole=proof[start:end]
assert 'rw [← AdaptiveQM40Context.literal_eq, ← AdaptiveQM38ResidualsDraft.sum_eq_literal]' in whole
assert 'Expr.evalRing_add, Expr.evalRing_mul' in whole
for j in range(29):assert f'have h{j:02d} := residual{j:02d} p v' in whole
for i in (20,24):assert f'have hdrop{i} := dropped{i} p v' in whole
simp='simp only ['+', '.join(f'h{j:02d}' for j in range(29))+', hdrop20, hdrop24, zero_mul, add_zero]'
assert simp in whole
assert 'theorem evaluation_cut : AdaptiveQM38EvaluationCutDraft.EvaluationCut' in proof
assert 'exact evaluation_identity CurrentWindowCarry2011.ports v' in proof
assert 'def EvaluationCut : Prop' in s['cut'] and 'parent.evalRing (fun i => ι (extend v i))' in s['cut']
assert 'child.evalRing (fun i => ι (v i))' in s['cut']
review=json.loads(s['external_graph_review']);assert review['all_29_residuals_match_parent_after_lift'] and review['removed_residuals_vanish_after_lift']
assert not re.search(r'^\s*(?:axiom|opaque)\b|\b(?:sorry|admit)\b',res+'\n'+proof,re.M)
print(json.dumps({'scope':'independent source composition/index and expression-DAG checks, with pinned external polynomial review; no Lean',
 'inputs':{n:{'path':p,'sha256':h} for n,(p,h) in sorted(files.items())},
 'matched_residuals':len(keep),'dropped_parent_indices':[20,24],
 'child_ordered_sum_ast_matches_literal':True,'evaluation_identity_source_for_arbitrary_ports':True,
 'specialization':'CurrentWindowCarry2011.ports','lean_elaboration':False},sort_keys=True,indent=2))
