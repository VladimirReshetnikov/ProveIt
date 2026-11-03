#!/usr/bin/env python3
"""Read-only audit of positive 91-to-90 draft witness transport."""
from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
if sys.flags.optimize:raise SystemExit('optimized Python refused')
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary12-direct-main-probe';O=P/'observations/forward-attempt01'; G=P/'observations/graph-attempt01/terminal.json';B=D/'research/ordinary12-qcube92-candidate/observations/halt2-attempt01/terminal.json'
pins={P/'FORWARD.md':'59a542168445a4f7fb6287653dc56f36c527329057b0827c926c5c220e0bc888',P/'DirectMainForward.lean':'de770e415209f42b1d0222a8e41edb573efe86cf0884ee88b786a6f536f6c491',P/'run-forward.py':'36012a79ca6daa453e7ab9f6f901fae06eb663c8d65c7c9affc8141d9c307274',O/'terminal.json':'d0ee9633116c763c60067bdf76b9fa6dbfb1d64c3f729772074611a1c909d3d9',O/'stdout':'402a36211dc469fa5c0a2fb13bde06187ede222963004b1c6394ac430053f11e',G:'6b1d05e8b34b8f5f701ad424b897bb996a9b2e519d08bd451ff1935b0e8e2c68',B:'8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f'}
def need(v,m):
 if not v:raise SystemExit(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def checkpins():
 for p,h in pins.items():need(sha(p)==h,'pin mismatch '+str(p))
checkpins();s=(P/'DirectMainForward.lean').read_text();r=json.loads((O/'terminal.json').read_text());g=json.loads(G.read_text())
need(s.splitlines()[0]=='import DirectMainGraph' and 'variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in s,'model/import mismatch')
need('def transform (v : Fin 12 → V) : Fin 12 → V := Function.update v 11 (v 11+v 5)' in s,'transformation mismatch')
z=s.split('theorem zero_iff',1)[1].split(':= by',1)[0]
for x in ('(p : Fin 4 → ℕ) (v : Fin 12 → V)','InternalZero (graph (integerPorts p)).output (transform v) ↔','InternalZero (FreeJXQ91.graph (integerPorts p)).output v'):need(x in z,'zero iff mismatch '+x)
pos=s.split('theorem transform_pos',1)[1].split(':= by',1)[0];need('(hv : ∀j,0<v j) : ∀j,0<transform v j' in pos,'positivity mismatch')
e=s.split('theorem exists_direct_of_xq91',1)[1].split(':= by',1)[0]
for x in ('(p : Fin 4 → ℕ)','∃v : Fin 12 → V, (∀j,0<v j) ∧ InternalZero (FreeJXQ91.graph (integerPorts p)).output v','∃v : Fin 12 → V, (∀j,0<v j) ∧ InternalZero (graph (integerPorts p)).output v'):need(x in e,'existence direction mismatch '+x)
need('rw [first_eval, main_eval, ordinary_eval]' in s and '(zero_iff p v).mpr hz' in s and 'set_option linter.' not in s,'proof/local lints mismatch')
need(r['exit']==0 and r['reason'] is None and r['union_unchanged'] and r['union_count']==1291 and r['base_receipt_sha256']==sha(B),'receipt failure')
need(r['source_sha256']==r['source_after']==sha(P/'DirectMainForward.lean')==sha(O/'source.txt') and r['runner_sha256']==r['runner_after']==sha(P/'run-forward.py'),'source/runner mismatch')
need(r['lean_sha256']==r['lean_after']==sha(r['command'][0]) and r['stdout_sha256']==sha(O/'stdout') and r['stderr_sha256']==sha(O/'stderr') and not (O/'stderr').read_bytes(),'Lean/log mismatch')
need((O/'stdout').read_text()==''.join(f"'DirectMainForward.{n}' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for n in ('zero_iff','transform_pos','exists_direct_of_xq91')),'axiom report mismatch')
out=Path(r['command'][r['command'].index('-o')+1]);src=Path(r['command'][r['command'].index('-o')-1]);need(sha(out)==r['object_sha256']=='46ace173cb7c23931d94b46fbf829ae86b69e16242d6ca88363000151be7e8fd' and sha(src)==sha(P/'DirectMainForward.lean'),'compiled object mismatch')
paths=r['lean_path'].split(':');graph=Path(paths[0])/'DirectMainGraph.olean';producer=Path(paths[1])/'XQ91.olean'
need(sha(graph)==r['graph_producer_sha256']==g['object_sha256'] and sha(producer)==r['xq91_producer_sha256']==g['xq91_producer_sha256'] and paths[1:]==g['lean_path'].split(':'),'provider mismatch')
need(len(r['samples'])==2 and all(x['mem_available_kib']>=8*1024**2 and len(x['lean'])<=2 for x in [r['preflight']]+r['samples']),'resource record mismatch')
prior=subprocess.run([sys.executable,'-I','-S','-B',str(D/'reviews/ordinary12-direct-main-graph-independent/check.py')],capture_output=True,check=True);need(not prior.stderr and json.loads(prior.stdout)['status']=='PASS','graph/provider review failed')
checkpins();need(sha(out)==r['object_sha256'] and sha(graph)==r['graph_producer_sha256'] and sha(producer)==r['xq91_producer_sha256'],'proof object changed')
print(json.dumps({'status':'PASS','zero_iff_at_transformed_valuation':True,'positive_forward_existence':True,'graph_and_1291_union_review':'PASS','scope':'forward existence only; no arbitrary reverse existence or iPRA proof'},indent=2))
