#!/usr/bin/env python3
"""Bounded source comparison for unelaborated residual-evaluation proposal."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,(str(p),hashlib.sha256(b).hexdigest());return b.decode()
pin(P/'generate.py','99826beb5b906850c6141dbf0dedbf7b3677d9fc98a12f76c4e1bb48fa7e48b2')
obs=json.loads(pin(P/'result.json','e82e3b66a5e3938cf08b902b8304d497d9f1746730d974c16f17c34be1dbf159'))
res=pin(P/'AdaptiveQM38Residuals.lean.src','d0bb6ab27fbd9f70c5e4faf529a725ae065bf9787b570a8c675c38d21460fa97')
proof=pin(P/'AdaptiveQM38ResidualEvaluation.lean.src','338fdf383779b3b9e155b0982700f609092b0e70109fc6c28482abefebd231ad')
old=pin(D/'Lean/DiophantineConsistency/AdaptiveQM40Context.lean','be48ed96bcb082715c99cd697bfa25ff21bd55aa789e868970b74e621422dece')
child=json.loads(pin(D/'research/adaptive-square-sums38-two-quadratic-products/candidate.json','ee523a8a821df163b038a19c4902234d3f09e730cbeee255dd4c896bdff7ae56'))
literal=pin(D/'research/adaptive-qm38-conditional-model-draft/AdaptiveQM38Literal.lean.src','f033af128e5ca4c7a5a1473e6370fc385d0354b110067ae84e168eed6643a44d')
cut=pin(D/'research/adaptive-qm38-conditional-model-draft/AdaptiveQM38EvaluationCut.lean.src','08707aa597d45389ab038fcda534d342ec4487913da52832ea441241fa9fee0b')
prior=json.loads(pin(D/'research/adaptive-square-sums38-two-quadratic-products/result.json','c480e61fd1a90a57ebc6fcb984f47eed7354d561c8b15dc0edf20934fa24e994'))
assert prior['all_29_residuals_exact_after_lift']
a=old.index('def residuals (p : Fin 4 → ℤ) : Fin 31 → Expr (Fin 40) :=');b=old.index('\ndef sum (p : Fin 4 → ℤ)',a);x=re.findall(r'  !\[([^\n]+)\]',old[a:b]);assert len(x)==1
parent=x[0].split(',');assert len(parent)==31 and parent[20]=='ellProductDifference' and parent[24]=='deltaProductDifference'
expected=[(i,n) for i,n in enumerate(parent) if i not in (20,24)]
actual=re.findall(r'/-- Parent residual (\d+) and retained child residual (\d+): ([A-Za-z0-9_]+)\. -/',proof)
assert len(actual)==29 and [(int(i),int(j),n) for i,j,n in actual]==[(i,j,n) for j,(i,n) in enumerate(expected)]
for j,(i,n) in enumerate(expected):
 assert f'theorem residual{j:02d} (p : Fin 4 → ℤ) (v : Fin 38 → V)' in proof
 assert f'(AdaptiveQM40Context.residuals p {i}).evalRing (fun k => ι (extend v k))' in proof
 assert f'(AdaptiveQM38ResidualsDraft.residuals p {j}).evalRing (fun k => ι (v k))' in proof
 assert f'h{j:02d} := residual{j:02d} p v' in proof
for i in (20,24):assert f'theorem dropped{i}' in proof and f'hdrop{i} := dropped{i} p v' in proof
vectors=re.findall(r'  !\[([^\n]+)\]',res);assert len(vectors)==1 and vectors[0].split(',')==[n for _,n in expected]
start=literal.index('  let J : Expr (Fin 38) := .var 0');end=literal.index('\n  -- END GENERATED ROWS',start)
body=literal[start:end].replace('  -- BEGIN GENERATED ROWS\n','');assert body in res
assert 'theorem sum_eq_literal' in res and 'theorem evaluation_identity' in proof and 'theorem evaluation_cut : AdaptiveQM38EvaluationCutDraft.EvaluationCut' in proof
assert 'def EvaluationCut : Prop' in cut and 'parent.evalRing (fun i => ι (extend v i))' in cut and 'child.evalRing (fun i => ι (v i))' in cut
# Reconstruct the child graph as an ordered arithmetic DAG and compare its
# output with a left-associated sum of the 29 named squares.
env={x:('leaf',x) for x in child['witnesses']+child['fixed_numerals']}
def v(x):return ('const',x) if type(x)==int else env[x]
for n,o,a,b in child['source']:env[n]=(o,v(a),v(b))
target=None
for _,n in expected:
 term=('*',env[n],env[n]);target=term if target is None else ('+',target,term)
assert target==env[child['output']] and obs['child_sum_exact_syntax']
print(json.dumps({'scope':'bounded text/ordered DAG checks for unelaborated proof source; no Lean or universal model theorem','retained_residuals':len(expected),'deleted_parent_residuals':[20,24],'child_output_exact_sum_dag':True,'actual_evaluation_proof_unelaborated':True,'earlier_external_exact_residual_receipt':True},indent=2,sort_keys=True))
