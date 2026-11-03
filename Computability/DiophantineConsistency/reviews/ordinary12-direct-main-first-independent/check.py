#!/usr/bin/env python3
"""Read-only review of direct-main first-residual extraction and provider."""
from pathlib import Path
from hashlib import sha256
import json, subprocess, sys
if sys.flags.optimize: raise SystemExit('optimized Python refused')
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary12-direct-main-probe';O=P/'observations/first-attempt03'; G=P/'observations/graph-attempt01/terminal.json';B=D/'research/ordinary12-qcube92-candidate/observations/halt2-attempt01/terminal.json'
pins={P/'FIRST.md':'b9a93d41065ccab1e44a11d5c81b107896c09e71cd26fb0b8f3980da09eeaa54',P/'DirectMainFirst.lean':'8dc77d35d1727e1228a015bc6e9494bc4c155666474a4103b0a1f650f5ce107d',P/'run-first.py':'448a9c93a20eea0c54757e5f050aa1e06791e239f5c231226f492dec9b374ba1',O/'terminal.json':'9896d230d5f06bf64c090567ed380b387d55f7f472430cd2a0a5b0d66c886264',O/'stdout':'ae8c3d40e325df274887b5b34617f86de45e695c92b449674e4f6fa1e33c6d63',G:'6b1d05e8b34b8f5f701ad424b897bb996a9b2e519d08bd451ff1935b0e8e2c68',B:'8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f'}
def need(v,m):
 if not v:raise SystemExit(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def checkpins():
 for p,h in pins.items():need(sha(p)==h,'pin mismatch '+str(p))
checkpins();s=(P/'DirectMainFirst.lean').read_text();g=(P/'DirectMainGraph.lean').read_text();r=json.loads((O/'terminal.json').read_text());gr=json.loads(G.read_text())
need(s.splitlines()[:3]==['import DirectMainGraph','import DiophantineConsistency.ArithmeticAdaptiveScaledNorms2011','import DiophantineConsistency.ArithmeticAdaptiveQuotients2011'],'imports changed')
need('variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in s,'model context changed')
a=s.split('def firstParts (p : Fin 4 → ℤ) : Expr (Fin 12) × Expr (Fin 12) :=',1)[1].split('\n  (Z, g42)',1)[0]
b=g.split('def graph (p : Fin 4 → ℤ) : Graph :=',1)[1].split('\n  let A0 := g38 - g42',1)[0]
need(a==b and '  let Z := g33 - Bt\n' in a and '  let g42 := g39 * g41' in a,'first root/shape source mismatch')
need('(graph p).first =\n    (firstParts p).1*(firstParts p).1-(firstParts p).2' in s,'first shape mismatch')
for name in ('first_zero','first_scaled_norm'):
 h=s.split('theorem '+name,1)[1].split(':= by',1)[0]
 need('(p : Fin 4 → ℕ) (v : Fin 12 → V)' in h and '(hz : InternalZero (graph (integerPorts p)).output v)' in h,'theorem input mismatch '+name)
 if name=='first_zero':need('InternalZero (graph (integerPorts p)).first v' in h,'first zero conclusion mismatch')
 else:
  for t in ('let q : V := 1+v 0*(p 0:V)','let X : V := q*v 5','let Y : V := (q*(q*q))*v 6','let k : V := v 8+v 9','let ell : V := (X*Y)*(Y*k)','let b : V := v 0*(p 0:V)','magnitude (pairEval (firstParts (integerPorts p)).1 v) *','magnitude (pairEval (firstParts (integerPorts p)).1 v) = b*b*(1+ell*(ell+k))'):need(t in h,'norm statement mismatch '+t)
need('sq_nonneg' in s and 'mul_self_eq_zero.mp h' in s and 'unit_square_norm' in s and 'rhs_pair p v' in s,'proof structure mismatch')
need(r['exit']==0 and r['reason'] is None and r['union_unchanged'] and r['union_count']==1291 and r['base_receipt_sha256']==sha(B),'receipt mismatch')
need(r['source_sha256']==r['source_after']==sha(P/'DirectMainFirst.lean')==sha(O/'source.txt') and r['runner_sha256']==r['runner_after']==sha(P/'run-first.py'),'source/runner mismatch')
need(r['lean_sha256']==r['lean_after']==sha(r['command'][0]) and r['stdout_sha256']==sha(O/'stdout') and r['stderr_sha256']==sha(O/'stderr') and not (O/'stderr').read_bytes(),'Lean/log mismatch')
need((O/'stdout').read_text()==''.join(f"'DirectMainFirst.{n}' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for n in ('first_zero','first_scaled_norm')),'axiom report mismatch')
out=Path(r['command'][r['command'].index('-o')+1]);src=Path(r['command'][r['command'].index('-o')-1]);need(sha(out)==r['object_sha256']=='e24c62d66d61d09135adf82c0b3d6b9b7297fcdffddbc0582fab10dbcb35b257' and sha(src)==sha(P/'DirectMainFirst.lean'),'compiled object mismatch')
paths=r['lean_path'].split(':');graph=Path(paths[0])/'DirectMainGraph.olean';producer=Path(paths[1])/'XQ91.olean'
need(sha(graph)==r['graph_producer_sha256']==gr['object_sha256'] and sha(producer)==r['xq91_producer_sha256']==gr['xq91_producer_sha256'] and paths[1:]==gr['lean_path'].split(':'),'provider mismatch')
need(len(r['samples'])==3 and all(x['mem_available_kib']>=8*1024**2 and len(x['lean'])<=2 for x in [r['preflight']]+r['samples']),'resource record mismatch')
for i in ('01','02'):
 obs=P/('observations/first-attempt'+i); f=json.loads((obs/'terminal.json').read_text());need(f['exit']!=0 and f['object_sha256'] is None and sha(obs/'source.txt')==f['source_sha256'] and sha(obs/'stdout')==f['stdout_sha256'] and sha(obs/'stderr')==f['stderr_sha256'] and 'error:' in (obs/'stdout').read_text(),'failed attempt record mismatch '+i)
prior=subprocess.run([sys.executable,'-I','-S','-B',str(D/'reviews/ordinary12-direct-main-graph-independent/check.py')],capture_output=True,check=True);need(not prior.stderr and json.loads(prior.stdout)['status']=='PASS','graph review failed')
checkpins();need(sha(out)==r['object_sha256'] and sha(graph)==r['graph_producer_sha256'] and sha(producer)==r['xq91_producer_sha256'],'object changed')
print(json.dumps({'status':'PASS','first_root_matches_graph_source':True,'first_zero_and_scaled_norm':True,'accepted_attempt':'03','earlier_failed_attempts':['01','02'],'graph_provider_review':'PASS','scope':'arbitrary natural ports and valuation in IΣ₁ models; no quotient, soundness, reverse or iPRA proof'},indent=2))
