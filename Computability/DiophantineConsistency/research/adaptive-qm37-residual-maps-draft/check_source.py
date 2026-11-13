#!/usr/bin/env python3
"""Bounded read-only residual/source audit; no Lean."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1];base=D/'research/adaptive-qm37-conditional-model-draft'
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,(str(p),hashlib.sha256(b).hexdigest());return b.decode()
pin(P/'generate.py','237c6c6a7619a163a6c6d348d297120d702175b8261514eef0b3b2fcf4f1de83')
obs=json.loads(pin(P/'result.json','e3aa1083655891a487fb0472b253195107cc10dbb65e4f8220e1310ba0152617'))
proof=pin(P/'AdaptiveQM37ResidualMaps.lean.src','967db1a4348b9110c1eeca74546029c94e7dbd6676e5bf0bd18e591bb758ad73')
parent=pin(D/'research/adaptive-qm38-residual-evaluation-draft/AdaptiveQM38Residuals.lean.src','d0bb6ab27fbd9f70c5e4faf529a725ae065bf9787b570a8c675c38d21460fa97')
child=pin(base/'AdaptiveQM37Residuals.lean.src','c1c0801c89f701b69b244dfed8c95ab5d289d1b309cb5e98fe28b064644efe3a')
pin(base/'AdaptiveQM37ConditionalTransfer.lean.src','be810ba3342ba05423e42e70eceff065809ba0380b804b79060b17ae73415566')
pin(base/'AdaptiveQM37DifferenceWitness.lean.src','b65647fb73619d6f52e166ae61233854a47e9f968174481f321f44bcdf915c80')
cert=json.loads(pin(D/'research/adaptive-square-sums37-difference-quartic/result.json','07ede5d8f22e400be9dd6ad478c8bc55281925d27edfd1e2b5f03bf41a7394be'))
def vec(s):
 x=re.findall(r'^  !\[([^\n]+)\]$',s,re.M);assert len(x)==1;return x[0].split(',')
a=vec(parent);b=vec(child);assert len(a)==29 and len(b)==28 and a[2]==b[2]=='auxResidual' and a[4]=='squareDifference' and a[21]=='ySquareDifference' and b[4]=='differenceEquality'
expected=[(a.index(n),j,n) for j,n in enumerate(b) if j not in (2,4)]
actual=re.findall(r'/-- Parent residual (\d+), child residual (\d+): ([A-Za-z0-9_]+)\. -/',proof)
assert [(int(i),int(j),n) for i,j,n in actual]==expected and len(expected)==26
for i,j,n in expected:
 assert f'theorem same{j:02d} (p : Fin 4 → ℤ) (v : Fin 37 → V)' in proof
 assert f'(AdaptiveQM38ResidualsDraft.residuals p {i}).evalRing (fun k => ι (extend v k))' in proof
 assert f'(AdaptiveQM37ResidualsDraft.residuals p {j}).evalRing (fun k => ι (v k))' in proof
for x in (4,21):assert f'theorem dropped{x:02d}' in proof
for x in ('theorem aux_relation','theorem project_difference','theorem extend_project','theorem extend_zero','theorem project_zero','theorem graphZeroObligations'):
 assert x in proof
assert 'ι (v 30) * (AdaptiveQM37ResidualsDraft.residuals p 4)' in proof
assert cert['parent_aux_equals_child_aux_plus_Q_times_difference_residual']
assert obs['common_residual_pairs']==26 and obs['dropped_parent_residuals']==[4,21]
print(json.dumps({'scope':'bounded source-index mapping and existing external residual observation only; no Lean/typechecking/model proof','common_residual_pairs':26,'parent_dropped_residuals':[4,21],'child_difference_residual':4,'special_auxiliary_relation_not_Lean_checked':True,'zero_map_proofs_unelaborated':True},indent=2,sort_keys=True))
