#!/usr/bin/env python3
"""Read-only review of direct graph first-factor transport bounds."""
from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
if sys.flags.optimize:raise SystemExit('optimized Python refused')
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary12-direct-main-probe';O=P/'observations/transport-attempt02'; F=P/'observations/transport-attempt01'; Q=P/'observations/quotient-attempt01/terminal.json'; B=D/'research/ordinary12-qcube92-candidate/observations/halt2-attempt01/terminal.json'
pins={P/'TRANSPORT.md':'17350dac00dc5395481609967d7b622f81679e6d59737dc4945650a960aa8620',P/'DirectMainTransport.lean':'032b363bef81b1815ffce40ae2b8d520e06f74a40296a3bdb70911ebfa05e71f',P/'run-transport.py':'d0a4b5da43bfc432c90acda6d9c52f0555b486ead472790197510258f062f908',O/'terminal.json':'7b59b6fce70f490c9fc698117210371cc1e8551f30f065c1e48ab91c847678f7',O/'stdout':'a75d70641c7c1283641304e0b4bfd19bd10056175dad24c39b95a29cc3f81980',F/'terminal.json':'a35227108854378e45798204ea929b9d0784343a8b3e6f5dfaa10708abebc0b1',F/'source.txt':'e2135b1a524d7144dfea19ed9863bdf2ddeaef38fe8849110ac359d5603bf61c',F/'stdout':'e2dd2c0dfbf18d4d59bd4021edfaf4ae50f8d6b2599d52c46b8cf1ca9df54d60',Q:'252b400e069deef01bdd7bcabd647606493817c90c9f376752fb92cb873fc5d4',B:'8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f'}
def need(v,m):
 if not v:raise SystemExit(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def checkpins():
 for p,h in pins.items():need(sha(p)==h,'pin mismatch '+str(p))
checkpins();s=(P/'DirectMainTransport.lean').read_text();r=json.loads((O/'terminal.json').read_text());q=json.loads(Q.read_text());f=json.loads((F/'terminal.json').read_text())
need(s.splitlines()[:2]==['import DirectMainFirstQuotient','import DiophantineConsistency.ArithmeticAdaptiveTransport2011'] and 'variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in s,'model/import mismatch')
a=s.split('theorem root_rep',1)[1].split(':= by',1)[0]
for t in ('(p : Fin 4 → ℕ) (v : Fin 12 → V)','let b : V := v 0*(p 0:V)','let q : V := 1+b','let ell : V := (X*Y)*(Y*k)','let W : V := 1+k*b','let A : V := (p 1:V)+v 5','let Bp : V := q*A','let Bn : V := (v 1+v 2)*A+v 1','Equivalent (pairEval (firstParts (integerPorts p)).1 v)','(b*(ell+k+v 7+v 6)+Bn*(W*q),Bp*(W*q))'):need(t in a,'root representation mismatch '+t)
h=s.split('theorem transport',1)[1].split(':= by',1)[0]
for t in ('(p : Fin 4 → ℕ) (v : Fin 12 → V)','(hb : 0<(p 0:V)) (hv : ∀j,0<v j)','(hz : InternalZero (graph (integerPorts p)).output v)','let q : V := 1+v 0*(p 0:V)','let A : V := (p 1:V)+v 5','(v 1+v 2)*A+v 1 < q*A ∧ 0<q-(v 1+v 2)'):need(t in h,'transport statement mismatch '+t)
for t in ('first_root p v hz hb0','first_root_bound ell k t he hk hn\'','magnitude_equivalent (root_rep p v)','by_contra hnle','tsub_pos_iff_lt.mpr hgap'):need(t in s,'proof element mismatch '+t)
need('set_option linter.' not in s,'unexpected local lint suppression')
need(r['exit']==0 and r['reason'] is None and r['union_unchanged'] and r['union_count']==1291 and r['base_receipt_sha256']==sha(B),'receipt failure')
need(r['source_sha256']==r['source_after']==sha(P/'DirectMainTransport.lean')==sha(O/'source.txt') and r['runner_sha256']==r['runner_after']==sha(P/'run-transport.py'),'source/runner mismatch')
need(r['lean_sha256']==r['lean_after']==sha(r['command'][0]) and r['stdout_sha256']==sha(O/'stdout') and r['stderr_sha256']==sha(O/'stderr') and not (O/'stderr').read_bytes(),'Lean/log mismatch')
need((O/'stdout').read_text()==''.join(f"'DirectMainTransport.{n}' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for n in ('root_rep','transport')),'axiom report mismatch')
out=Path(r['command'][r['command'].index('-o')+1]);src=Path(r['command'][r['command'].index('-o')-1]);need(sha(out)==r['object_sha256']=='8cb15f06eb7f306048d084e85937d25b625356ed24d0b21ec027086543880d72' and sha(src)==sha(P/'DirectMainTransport.lean'),'compiled object mismatch')
paths=r['lean_path'].split(':');names=('DirectMainFirstQuotient','DirectMainFirst','DirectMainGraph','XQ91');keys=('quotient_producer_sha256','first_producer_sha256','graph_producer_sha256','xq91_producer_sha256');objects=[Path(p)/(n+'.olean') for p,n in zip(paths,names)]
need(paths[1:]==q['lean_path'].split(':') and all(sha(p)==r[k] for p,k in zip(objects,keys)) and r['quotient_producer_sha256']==q['object_sha256'] and all(r[k]==q[k] for k in keys[1:]),'provider mismatch')
need(len(r['samples'])==4 and all(x['mem_available_kib']>=8*1024**2 and len(x['lean'])<=2 for x in [r['preflight']]+r['samples']),'resource record mismatch')
need(f['exit']!=0 and f['object_sha256'] is None and sha(F/'source.txt')==f['source_sha256'] and sha(F/'stdout')==f['stdout_sha256'] and sha(F/'stderr')==f['stderr_sha256'] and 'error:' in (F/'stdout').read_text() and 'sorryAx' in (F/'stdout').read_text(),'failed attempt mismatch')
prior=subprocess.run([sys.executable,'-I','-S','-B',str(D/'reviews/ordinary12-direct-main-quotient-independent/check.py')],capture_output=True,check=True);need(not prior.stderr and json.loads(prior.stdout)['status']=='PASS','quotient/provider review failed')
checkpins();need(sha(out)==r['object_sha256'] and all(sha(p)==r[k] for p,k in zip(objects,keys)),'proof object changed')
print(json.dumps({'status':'PASS','positive_beta_and_all_witnesses_required':True,'graph_zero_required':True,'strict_transport_bounds':True,'failed_attempt_01':'error and sorryAx','accepted_attempt':'02','quotient_and_1291_union_review':'PASS','scope':'model-level first-factor bounds, no graph soundness or iPRA proof'},indent=2))
