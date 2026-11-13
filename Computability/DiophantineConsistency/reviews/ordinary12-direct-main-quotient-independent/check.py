#!/usr/bin/env python3
"""Read-only review of positive first Pell root from draft graph zero."""
from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
if sys.flags.optimize:raise SystemExit('optimized Python refused')
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary12-direct-main-probe';O=P/'observations/quotient-attempt01';F=P/'observations/first-attempt03/terminal.json';G=P/'observations/graph-attempt01/terminal.json';B=D/'research/ordinary12-qcube92-candidate/observations/halt2-attempt01/terminal.json'
pins={P/'QUOTIENT.md':'4e9c6634e103a5e206953116e8b5193cfa29403c4856fbdce52820ff7cc81431',P/'DirectMainFirstQuotient.lean':'a9a05ee1b896045b754f3285759a7163c297fd14d3d5aafc1b20a57566139ccb',P/'run-quotient.py':'b08f326080d974505b3571147c7959c8638006d52bcc0e97aa79a7ed1a77171a',O/'terminal.json':'252b400e069deef01bdd7bcabd647606493817c90c9f376752fb92cb873fc5d4',O/'stdout':'2b5882c8bbdea526897274ad16ada1203e09741ef3f73666dede6884450e6af0',F:'9896d230d5f06bf64c090567ed380b387d55f7f472430cd2a0a5b0d66c886264',G:'6b1d05e8b34b8f5f701ad424b897bb996a9b2e519d08bd451ff1935b0e8e2c68',B:'8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f'}
def need(v,m):
 if not v:raise SystemExit(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def checkpins():
 for p,h in pins.items():need(sha(p)==h,'pin mismatch '+str(p))
checkpins();s=(P/'DirectMainFirstQuotient.lean').read_text();r=json.loads((O/'terminal.json').read_text());f=json.loads(F.read_text());g=json.loads(G.read_text())
need(s.splitlines()[0]=='import DirectMainFirst' and 'variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in s,'import/model mismatch')
h=s.split('theorem first_root',1)[1].split(':= by',1)[0]
for t in ('(p : Fin 4 → ℕ) (v : Fin 12 → V)','(hz : InternalZero (graph (integerPorts p)).output v)','(hb : 0<v 0*(p 0:V))','let q : V := 1+v 0*(p 0:V)','let X : V := q*v 5','let Y : V := (q*(q*q))*v 6','let k : V := v 8+v 9','let Q : V := (X*Y)*Y','∃ first : V, 0<first ∧','magnitude (pairEval (firstParts (integerPorts p)).1 v) = (v 0*(p 0:V))*first ∧','first*first=1+Q*(Q+1)*k*k'):need(t in h,'statement mismatch '+t)
for t in ('first_scaled_norm p v hz','scaled_quotient','hb hs','pos_of_mul_pos_left','dsimp [ell,Q]; ring'):need(t in s,'proof ingredient missing '+t)
need(r['exit']==0 and r['reason'] is None and r['union_unchanged'] and r['union_count']==1291 and r['base_receipt_sha256']==sha(B),'receipt failure')
need(r['source_sha256']==r['source_after']==sha(P/'DirectMainFirstQuotient.lean')==sha(O/'source.txt') and r['runner_sha256']==r['runner_after']==sha(P/'run-quotient.py'),'source/runner mismatch')
need(r['lean_sha256']==r['lean_after']==sha(r['command'][0]) and r['stdout_sha256']==sha(O/'stdout') and r['stderr_sha256']==sha(O/'stderr') and not (O/'stderr').read_bytes(),'Lean/log mismatch')
need((O/'stdout').read_text()=="'DirectMainFirstQuotient.first_root' depends on axioms: [propext, Classical.choice, Quot.sound]\n",'axiom report mismatch')
out=Path(r['command'][r['command'].index('-o')+1]);src=Path(r['command'][r['command'].index('-o')-1]);need(sha(out)==r['object_sha256']=='8abb2bb6723d14abc3fadbb83e45fa067ffcc0d042110a40fc84511ef90bfee5' and sha(src)==sha(P/'DirectMainFirstQuotient.lean'),'compiled object mismatch')
paths=r['lean_path'].split(':');first=Path(paths[0])/'DirectMainFirst.olean';graph=Path(paths[1])/'DirectMainGraph.olean';xq=Path(paths[2])/'XQ91.olean'
need(paths[1:]==f['lean_path'].split(':') and paths[2:]==g['lean_path'].split(':') and sha(first)==r['first_producer_sha256']==f['object_sha256'] and sha(graph)==r['graph_producer_sha256']==f['graph_producer_sha256']==g['object_sha256'] and sha(xq)==r['xq91_producer_sha256']==g['xq91_producer_sha256'],'producer mismatch')
need(len(r['samples'])==2 and all(x['mem_available_kib']>=8*1024**2 and len(x['lean'])<=2 for x in [r['preflight']]+r['samples']),'resource record mismatch')
prior=subprocess.run([sys.executable,'-I','-S','-B',str(D/'reviews/ordinary12-direct-main-first-independent/check.py')],capture_output=True,check=True);need(not prior.stderr and json.loads(prior.stdout)['status']=='PASS','first norm/provider review failed')
checkpins();need(sha(out)==r['object_sha256'] and sha(first)==r['first_producer_sha256'] and sha(graph)==r['graph_producer_sha256'] and sha(xq)==r['xq91_producer_sha256'],'proof object changed')
print(json.dumps({'status':'PASS','graph_zero_and_positive_b_required':True,'positive_first_root_and_norm':True,'first_graph_and_1291_union_review':'PASS','scope':'first factor only, no graph soundness or iPRA proof'},indent=2))
