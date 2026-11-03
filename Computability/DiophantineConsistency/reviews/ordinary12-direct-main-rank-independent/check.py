#!/usr/bin/env python3
"""Read-only review of graph-specific rank divisibility."""
from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
if sys.flags.optimize:raise SystemExit('optimized Python refused')
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary12-direct-main-probe';O=P/'observations/rank-attempt01';I=P/'observations/indices-attempt03/terminal.json';B=D/'research/ordinary12-qcube92-candidate/observations/halt2-attempt01/terminal.json'
pins={P/'RANK.md':'974d1b51bff81d8b51b726ef220adab2f7782519563bbb1510c5378741174502',P/'DirectMainRank.lean':'0f82f4e72359980aba19e1f20bf92eadd324a7b74f4c096f1a3144d6db600b41',P/'run-rank.py':'b53288cd1411f7db386c7ce8285f91bbd34a8d5ea576a6dc99e00996fea03b7b',O/'terminal.json':'b9f38de8fdd47de67be0bab98728ce434be51865ecb645bce326caf73a438148',O/'stdout':'957b44e09fddaa7d26f223df3e71124bb46979fa862c8af5cb9d3396ce70a332',I:'d03cf9f90629a488bc08fff66d75eed0165d0a79d444192f790d0a0491bd0ad6',B:'8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f'}
def need(v,m):
 if not v:raise SystemExit(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def checkpins():
 for p,h in pins.items():need(sha(p)==h,'pin mismatch '+str(p))
checkpins();s=(P/'DirectMainRank.lean').read_text();r=json.loads((O/'terminal.json').read_text());i=json.loads(I.read_text())
need(s.splitlines()[:2]==['import DirectMainIndices','import DiophantineConsistency.ArithmeticAdaptiveRankCongruence2011'] and 'variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in s,'model/import mismatch')
a=s.split('theorem rank_of_balance',1)[1].split(':= by',1)[0]
for x in ('(q Y X a c H G R k s main : V)','(hq : 0<q) (hy : Y=q^3*s) (hH : H=3+4*Y*(X+1))','(he : H*(R+1)+q^5*(s*(X+a*c+H*G)) = H*k+q^5*(s*main))','q^4 ∣ magnitude (R+1,k)'):need(x in a,'balance theorem mismatch '+x)
h=s.split('theorem graph_rank',1)[1].split(':= by',1)[0]
for x in ('(p : Fin 4 → ℕ) (v : Fin 12 → V)','(hb : 0<(p 0:V)) (hv : ∀j,0<v j)','(hz : InternalZero (graph (DirectMainFirst.integerPorts p)).output v)','let b : V := v 0*(p 0:V)','let q : V := 1+b','let k : V := v 8+v 9','let R : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)','q^4 ∣ magnitude (R+1,k)'):need(x in h,'graph theorem mismatch '+x)
for x in ('mod_add_mul\'','dvd_magnitude_of_mod hm5 hemod','cancel_factor_three q Y X _ hq hY hdiv','DirectMainIndices.graph_indices p v hb hv hz','rank_of_balance q Y X a c H (v 11) R k (v 6) main hq hy hH he'):need(x in s,'proof linkage mismatch '+x)
need('set_option linter.' not in s,'unexpected local lint suppression')
need(r['exit']==0 and r['reason'] is None and r['union_unchanged'] and r['union_count']==1291 and r['base_receipt_sha256']==sha(B),'receipt failure')
need(r['source_sha256']==r['source_after']==sha(P/'DirectMainRank.lean')==sha(O/'source.txt') and r['runner_sha256']==r['runner_after']==sha(P/'run-rank.py'),'source/runner mismatch')
need(r['lean_sha256']==r['lean_after']==sha(r['command'][0]) and r['stdout_sha256']==sha(O/'stdout') and r['stderr_sha256']==sha(O/'stderr') and not (O/'stderr').read_bytes(),'Lean/log mismatch')
need((O/'stdout').read_text()==''.join(f"'DirectMainRank.{name}' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for name in ('rank_of_balance','graph_rank')),'axiom report mismatch')
out=Path(r['command'][r['command'].index('-o')+1]);src=Path(r['command'][r['command'].index('-o')-1]);need(sha(out)==r['object_sha256']=='bf4d176eddc731e0735be39f57440d1ee991d348563e62b8aaa8ecb216f28fef' and sha(src)==sha(P/'DirectMainRank.lean'),'compiled object mismatch')
paths=r['lean_path'].split(':');names=('DirectMainIndices','DirectMainOriented','DirectMainPell','DirectMainNorm','DirectMainProjection','DirectMainMain','DirectMainTransport','DirectMainFirstQuotient','DirectMainFirst','DirectMainGraph','XQ91');keys=('indices_producer_sha256','oriented_producer_sha256','pell_producer_sha256','norm_producer_sha256','projection_producer_sha256','main_producer_sha256','transport_producer_sha256','quotient_producer_sha256','first_producer_sha256','graph_producer_sha256','xq91_producer_sha256');objects=[Path(p)/(name+'.olean') for p,name in zip(paths,names)]
need(paths[1:]==i['lean_path'].split(':') and all(sha(p)==r[k] for p,k in zip(objects,keys)) and r[keys[0]]==i['object_sha256'] and all(r[k]==i[k] for k in keys[1:]),'provider mismatch')
need(len(r['samples'])==3 and all(x['mem_available_kib']>=8*1024**2 and len(x['lean'])<=2 for x in [r['preflight']]+r['samples']),'resource record mismatch')
prior=subprocess.run([sys.executable,'-I','-S','-B',str(D/'reviews/ordinary12-direct-main-indices-independent/check.py')],capture_output=True,check=True);need(not prior.stderr and json.loads(prior.stdout)['status']=='PASS','indices/provider review failed')
checkpins();need(sha(out)==r['object_sha256'] and all(sha(p)==r[k] for p,k in zip(objects,keys)),'proof object changed')
print(json.dumps({'status':'PASS','graph_zero_positive_beta_and_witnesses_required':True,'conclusion':'q^4 divides magnitude(R+1,k)','selected_producers_match':11,'indices_and_1291_union_review':'PASS','scope':'model-level divisibility, no index alignment or iPRA proof'},indent=2))
