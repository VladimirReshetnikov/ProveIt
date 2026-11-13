#!/usr/bin/env python3
"""Read-only review of graph-specific signed main norm and its receipts."""
from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
if sys.flags.optimize:raise SystemExit('optimized Python refused')
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary12-direct-main-probe';O=P/'observations/oriented-attempt02';F=P/'observations/oriented-attempt01'; M=P/'observations/main-attempt01/terminal.json';T=P/'observations/transport-attempt02/terminal.json';B=D/'research/ordinary12-qcube92-candidate/observations/halt2-attempt01/terminal.json'
pins={P/'ORIENTED.md':'fde74bea94d5213796f3dbfd8e528f75562c25d8d6bd7c6eaffdd6c305d49d8d',P/'DirectMainOriented.lean':'1bcffc13a61b2afc5e36e0d437120459bb1582c8f6beea809589ecaab3436a18',P/'DirectMainNorm.lean':'738c9a708950bca11bccb1904fe9d79192f85939f76c9bab6a0a549f3af74400',P/'run-oriented.py':'2d21f99f44d86046411b73e778f0ae91423a19d2d81911c57612a5ab60368ddb',O/'terminal.json':'03b3137c0763f25f59edcb375c7f01f795c1ad9f35ac8512dfd8c4e6156b308e',O/'stdout':'62183d9b4e1fd22147a054c24e05c9e537822adfd01a5a13b6db899e1cf7fd7d',F/'terminal.json':'eee1ccfe7ca8471004b51cdb1c6f64f0ce3f27e75ad8624b5d185386c1d8cdd2',F/'source.txt':'c4c19764ceb9becae79babffd18196bacabf8c904fd07906eab7326f732b58b2',F/'stdout':'ac845fa37ae6b07b3886438b7c013f05ef6a4045e88410eccc09c7ae26c6f034',M:'49a283a031049f02befb5ac76745b35fbb39b5c61a02544014c414526d829e56',T:'7b59b6fce70f490c9fc698117210371cc1e8551f30f065c1e48ab91c847678f7',B:'8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f'}
def need(v,m):
 if not v:raise SystemExit(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def checkpins():
 for p,h in pins.items():need(sha(p)==h,'pin mismatch '+str(p))
checkpins();s=(P/'DirectMainOriented.lean').read_text();n=(P/'DirectMainNorm.lean').read_text();r=json.loads((O/'terminal.json').read_text());m=json.loads(M.read_text());t=json.loads(T.read_text());f=json.loads((F/'terminal.json').read_text())
need(s.splitlines()[:2]==['import DirectMainMain','import DirectMainTransport'] and 'variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in s,'model/import mismatch')
a=s.split('theorem main_root_rep',1)[1].split(':= by',1)[0];h=s.split('theorem direct_norm',1)[1].split(':= by',1)[0]
for part in (a,h):
 for x in ('(p : Fin 4 → ℕ) (v : Fin 12 → V)','let b : V := v 0*(p 0:V)','let q : V := 1+b','let X : V := q*v 5','let Y : V := (q*(q*q))*v 6','let U : V := Y*(q*q)','let k : V := v 8+v 9','let c : V := v 8+Y*k','let a : V := X*Y+Y','let H : V := 3+4*a','let R : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)'):need(x in part,'definition mismatch '+x)
need('(hq : 1≤1+v 0*(p 0:V)) (hF : v 1≤1+v 0*(p 0:V))' in a and 'Equivalent (pairEval (DirectMainMain.mainParts (DirectMainMain.integerPorts p)).1 v)' in a and '(U*(X+a*c)+H*(U*v 11+R+1),H*k)' in a,'signed-pair theorem mismatch')
for x in ('(hb : 0<(p 0:V)) (hv : ∀j,0<v j)','(hz : InternalZero (graph (DirectMainFirst.integerPorts p)).output v)','magnitude (U*(X+a*c)+H*(U*v 11+R+1),H*k) *','magnitude (U*(X+a*c)+H*(U*v 11+R+1),H*k) = U*U*(1+(H+a*a)*(c*c))'):need(x in h,'direct norm mismatch '+x)
for x in ('DirectMainTransport.transport p v hb hv hz','magnitude_equivalent (main_root_rep p v hq hF)','DirectMainMain.main_scaled_norm p v hz'):need(x in s,'proof linkage mismatch '+x)
need('set_option linter.' not in s,'unexpected local lint suppression')
norm=n.split('theorem direct_main_orientation',1)[1].split(':= by',1)[0]
for x in ('(hU : 0<U) (hY : 8≤Y) (hk : 0<k)','let a := X*Y+Y','let c := eta+Y*k','let H := 3+4*a','let P := U*(X+a*c)+H*(U*G+R+1)','let N := H*k','magnitude (P,N)*magnitude (P,N)=U*U*(1+(H+a*a)*(c*c))'):need(x in norm,'conditional lemma comparison mismatch '+x)
need(r['exit']==0 and r['reason'] is None and r['union_unchanged'] and r['union_count']==1291 and r['base_receipt_sha256']==sha(B),'receipt failure')
need(r['source_sha256']==r['source_after']==sha(P/'DirectMainOriented.lean')==sha(O/'source.txt') and r['runner_sha256']==r['runner_after']==sha(P/'run-oriented.py'),'source/runner mismatch')
need(r['lean_sha256']==r['lean_after']==sha(r['command'][0]) and r['stdout_sha256']==sha(O/'stdout') and r['stderr_sha256']==sha(O/'stderr') and not (O/'stderr').read_bytes(),'Lean/log mismatch')
need((O/'stdout').read_text()==''.join(f"'DirectMainOriented.{x}' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for x in ('main_root_rep','direct_norm')),'axiom report mismatch')
out=Path(r['command'][r['command'].index('-o')+1]);src=Path(r['command'][r['command'].index('-o')-1]);need(sha(out)==r['object_sha256']=='10254beaf0ac3b44d3c65abac44c36cd0196aab6cca74ebc269a4d1b8660f521' and sha(src)==sha(P/'DirectMainOriented.lean'),'compiled object mismatch')
paths=r['lean_path'].split(':');names=('DirectMainMain','DirectMainTransport','DirectMainFirstQuotient','DirectMainFirst','DirectMainGraph','XQ91');keys=('main_producer_sha256','transport_producer_sha256','quotient_producer_sha256','first_producer_sha256','graph_producer_sha256','xq91_producer_sha256');objects=[Path(p)/(n+'.olean') for p,n in zip(paths,names)]
need(paths[2:]==t['lean_path'].split(':') and paths[4:]==m['lean_path'].split(':') and all(sha(p)==r[k] for p,k in zip(objects,keys)) and r[keys[0]]==m['object_sha256'] and r[keys[1]]==t['object_sha256'] and all(r[k]==t[k] for k in keys[2:]),'provider mismatch')
need(len(r['samples'])==2 and all(x['mem_available_kib']>=8*1024**2 and len(x['lean'])<=2 for x in [r['preflight']]+r['samples']),'resource record mismatch')
need(f['exit']!=0 and f['object_sha256'] is None and sha(F/'source.txt')==f['source_sha256'] and sha(F/'stdout')==f['stdout_sha256'] and sha(F/'stderr')==f['stderr_sha256'] and 'error' in (F/'stdout').read_text() and 'sorryAx' in (F/'stdout').read_text(),'failed attempt mismatch')
for review in ('ordinary12-direct-main-main-independent','ordinary12-direct-main-transport-independent'):
 prior=subprocess.run([sys.executable,'-I','-S','-B',str(D/'reviews'/review/'check.py')],capture_output=True,check=True);need(not prior.stderr and json.loads(prior.stdout)['status']=='PASS','prior review failed '+review)
checkpins();need(sha(out)==r['object_sha256'] and all(sha(p)==r[k] for p,k in zip(objects,keys)),'proof object changed')
print(json.dumps({'status':'PASS','main_rep_requires_q_and_F_bounds':True,'draft_zero_and_positive_beta_and_witnesses_required':True,'norm_matches_conditional_orientation_hypothesis':True,'failed_attempt_01':'error and sorryAx','accepted_attempt':'02','main_transport_and_1291_union_reviews':'PASS','scope':'model-level signed norm, no full graph soundness or iPRA proof'},indent=2))
