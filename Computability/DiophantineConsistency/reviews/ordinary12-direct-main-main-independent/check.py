#!/usr/bin/env python3
"""Read-only review of direct-main main-residual extraction and provider."""
from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
if sys.flags.optimize:raise SystemExit('optimized Python refused')
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary12-direct-main-probe';O=P/'observations/main-attempt01';G=P/'observations/graph-attempt01/terminal.json';B=D/'research/ordinary12-qcube92-candidate/observations/halt2-attempt01/terminal.json'
pins={P/'MAIN.md':'aae405f59cd5f2f46a840e21cbbe06510255358bab4cee955529e0225f906fa2',P/'DirectMainMain.lean':'a3aa8b924dd535be3cc4ff71f8de3f441287a843c82b46af38b6864347845234',P/'run-main.py':'1894f95edf145412f8a737c120ef92fb99b45125d5e3b01bd2ef04b07f14cdf2',O/'terminal.json':'49a283a031049f02befb5ac76745b35fbb39b5c61a02544014c414526d829e56',O/'stdout':'cc3c1c8791877cc8d48f90d2223c230cfa16501fd47097628c72ef64ca294981',G:'6b1d05e8b34b8f5f701ad424b897bb996a9b2e519d08bd451ff1935b0e8e2c68',B:'8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f'}
def need(v,m):
 if not v:raise SystemExit(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def checkpins():
 for p,h in pins.items():need(sha(p)==h,'pin mismatch '+str(p))
checkpins();s=(P/'DirectMainMain.lean').read_text();g=(P/'DirectMainGraph.lean').read_text();r=json.loads((O/'terminal.json').read_text());gr=json.loads(G.read_text())
need(s.splitlines()[:3]==['import DirectMainGraph','import DiophantineConsistency.ArithmeticAdaptiveScaledNorms2011','import DiophantineConsistency.ArithmeticAdaptiveQuotients2011'],'imports changed')
need('variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in s,'model context changed')
a=s.split('def mainParts (p : Fin 4 → ℤ) : Expr (Fin 12) × Expr (Fin 12) :=',1)[1].split('\n  (Dstar, g65)',1)[0]
b=g.split('def graph (p : Fin 4 → ℤ) : Graph :=',1)[1].split('\n  let A1 := g61 - g65',1)[0]
need(a==b and '  let Dstar := g58 + g59\n' in a and '  let g65 := g62 * g64' in a,'main root/shape source mismatch')
need('(graph p).main =\n    (mainParts p).1*(mainParts p).1-(mainParts p).2' in s,'main shape mismatch')
for name in ('main_zero','main_scaled_norm'):
 h=s.split('theorem '+name,1)[1].split(':= by',1)[0]
 need('(p : Fin 4 → ℕ) (v : Fin 12 → V)' in h and '(hz : InternalZero (graph (integerPorts p)).output v)' in h,'theorem input mismatch '+name)
 if name=='main_zero':need('InternalZero (graph (integerPorts p)).main v' in h,'main zero conclusion mismatch')
 else:
  for t in ('let q : V := 1+v 0*(p 0:V)','let X : V := q*v 5','let Y : V := (q*(q*q))*v 6','let U : V := Y*(q*q)','let k : V := v 8+v 9','let c : V := v 8+Y*k','let a : V := X*Y+Y','let H : V := 3+4*a','magnitude (pairEval (mainParts (integerPorts p)).1 v) *','magnitude (pairEval (mainParts (integerPorts p)).1 v) = U*U*(1+(H+a*a)*(c*c))'):need(t in h,'norm statement mismatch '+t)
need('sq_nonneg' in s and 'mul_self_eq_zero.mp h' in s and 'unit_square_norm' in s and 'rhs_pair p v' in s,'proof structure mismatch')
need('set_option linter.unusedVariables false' in s and 'set_option linter.unusedSimpArgs false' in s,'linter configuration mismatch')
need(r['exit']==0 and r['reason'] is None and r['union_unchanged'] and r['union_count']==1291 and r['base_receipt_sha256']==sha(B),'receipt mismatch')
need(r['source_sha256']==r['source_after']==sha(P/'DirectMainMain.lean')==sha(O/'source.txt') and r['runner_sha256']==r['runner_after']==sha(P/'run-main.py'),'source/runner mismatch')
need(r['lean_sha256']==r['lean_after']==sha(r['command'][0]) and r['stdout_sha256']==sha(O/'stdout') and r['stderr_sha256']==sha(O/'stderr') and not (O/'stderr').read_bytes(),'Lean/log mismatch')
need((O/'stdout').read_text()==''.join(f"'DirectMainMain.{n}' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for n in ('main_zero','main_scaled_norm')),'axiom report mismatch')
out=Path(r['command'][r['command'].index('-o')+1]);src=Path(r['command'][r['command'].index('-o')-1]);need(sha(out)==r['object_sha256']=='61ff9f8218a430bc84fc39399f3ee1421c267d42c0a1a7e6cbc40f066048d17d' and sha(src)==sha(P/'DirectMainMain.lean'),'compiled object mismatch')
paths=r['lean_path'].split(':');graph=Path(paths[0])/'DirectMainGraph.olean';producer=Path(paths[1])/'XQ91.olean'
need(sha(graph)==r['graph_producer_sha256']==gr['object_sha256'] and sha(producer)==r['xq91_producer_sha256']==gr['xq91_producer_sha256'] and paths[1:]==gr['lean_path'].split(':'),'provider mismatch')
need(len(r['samples'])==3 and all(x['mem_available_kib']>=8*1024**2 and len(x['lean'])<=2 for x in [r['preflight']]+r['samples']),'resource record mismatch')
prior=subprocess.run([sys.executable,'-I','-S','-B',str(D/'reviews/ordinary12-direct-main-graph-independent/check.py')],capture_output=True,check=True);need(not prior.stderr and json.loads(prior.stdout)['status']=='PASS','graph review failed')
checkpins();need(sha(out)==r['object_sha256'] and sha(graph)==r['graph_producer_sha256'] and sha(producer)==r['xq91_producer_sha256'],'object changed')
print(json.dumps({'status':'PASS','main_root_matches_graph_source':True,'main_zero_and_scaled_signed_pair_norm':True,'graph_provider_review':'PASS','scope':'arbitrary natural ports and valuation in IΣ₁ models; no ordered-pair identification, soundness, reverse or iPRA proof'},indent=2))
