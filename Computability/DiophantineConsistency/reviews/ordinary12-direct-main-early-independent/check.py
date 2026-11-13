#!/usr/bin/env python3
"""Read-only review of conditional early-index congruence."""
from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
if sys.flags.optimize:raise SystemExit('optimized Python refused')
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary12-direct-main-probe';O=P/'observations/early-attempt01';R=P/'observations/rank-attempt01/terminal.json';B=D/'research/ordinary12-qcube92-candidate/observations/halt2-attempt01/terminal.json'
pins={P/'EARLY.md':'db4dc952cd70042cacfc4f70446c968ee57cf5e905277ae827822b05d0cd8fdf',P/'DirectMainEarly.lean':'a00437e30cc44d00c9765ee816f912d022234ae6f163ff2ececb436124866824',P/'run-early.py':'f2861689702e8fa31bc9a0927a10e7eabbee5dc3142e955779f1069757b0d7d7',O/'terminal.json':'0507db7193667baf529fc62bf1f80063530296516e668f61e68670e0b305d357',O/'stdout':'eafb0f1b90c31cc220cf189fc77429ad751cc47541ef92e0cead44ed4a554118',R:'b9f38de8fdd47de67be0bab98728ce434be51865ecb645bce326caf73a438148',B:'8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f'}
def need(v,m):
 if not v:raise SystemExit(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def checkpins():
 for p,h in pins.items():need(sha(p)==h,'pin mismatch '+str(p))
checkpins();s=(P/'DirectMainEarly.lean').read_text();r=json.loads((O/'terminal.json').read_text());rank=json.loads(R.read_text())
need(s.splitlines()[:2]==['import DirectMainRank','import DiophantineConsistency.ArithmeticPellCongruences'] and 'variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in s,'model/import mismatch')
h=s.split('theorem early_of_window',1)[1].split(':= by',1)[0]
for x in ('(p : Fin 4 → ℕ) (v : Fin 12 → V)','(hb : 0<(p 0:V)) (hv : ∀j,0<v j)','(hz : InternalZero (graph (DirectMainFirst.integerPorts p)).output v)','(hw : let b : V := v 0*(p 0:V); let q : V := 1+b;','24≤R ∧ R+q^3+q+1≤q^4','let X : V := q*v 5','let Y : V := (q*(q*q))*v 6','let k : V := v 8+v 9','let c : V := v 8+Y*k','let a : V := X*Y+Y','let Q : V := (X*Y)*Y','let R : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)','∃ first main n m : V, 0<first ∧ 0<main ∧ 13≤n ∧ 0<m ∧ n≤k ∧ m≤c ∧','xcoord n (2*(Q-1)+1)=first ∧ 2*ycoord n (2*(Q-1)+1)=k ∧','xcoord m a=main ∧ ycoord m a=c ∧ (2*n)%(q^4)=R+1 ∧ R+1≤2*n ∧ R+1≤k'):need(x in h,'theorem mismatch '+x)
for x in ('DirectMainIndices.graph_indices p v hb hv hz','DirectMainRank.graph_rank p v hb hv hz','residue_quotients n B (q^4) hdiv','magnitude_mod (R+1,k) (q^4) hmod hc','obtain ⟨hR24,hupper⟩ := hw'):need(x in s,'proof linkage mismatch '+x)
need('set_option linter.' not in s,'unexpected local lint suppression')
need(r['exit']==0 and r['reason'] is None and r['union_unchanged'] and r['union_count']==1291 and r['base_receipt_sha256']==sha(B),'receipt failure')
need(r['source_sha256']==r['source_after']==sha(P/'DirectMainEarly.lean')==sha(O/'source.txt') and r['runner_sha256']==r['runner_after']==sha(P/'run-early.py'),'source/runner mismatch')
need(r['lean_sha256']==r['lean_after']==sha(r['command'][0]) and r['stdout_sha256']==sha(O/'stdout') and r['stderr_sha256']==sha(O/'stderr') and not (O/'stderr').read_bytes(),'Lean/log mismatch')
need((O/'stdout').read_text()=="'DirectMainEarly.early_of_window' depends on axioms: [propext, Classical.choice, Quot.sound]\n",'axiom report mismatch')
out=Path(r['command'][r['command'].index('-o')+1]);src=Path(r['command'][r['command'].index('-o')-1]);need(sha(out)==r['object_sha256']=='66068b403029ab3557227f509f3a92d51164347c399125b235af41112260b8a5' and sha(src)==sha(P/'DirectMainEarly.lean'),'compiled object mismatch')
paths=r['lean_path'].split(':');names=('DirectMainRank','DirectMainIndices','DirectMainOriented','DirectMainPell','DirectMainNorm','DirectMainProjection','DirectMainMain','DirectMainTransport','DirectMainFirstQuotient','DirectMainFirst','DirectMainGraph','XQ91');keys=('rank_producer_sha256','indices_producer_sha256','oriented_producer_sha256','pell_producer_sha256','norm_producer_sha256','projection_producer_sha256','main_producer_sha256','transport_producer_sha256','quotient_producer_sha256','first_producer_sha256','graph_producer_sha256','xq91_producer_sha256');objects=[Path(p)/(name+'.olean') for p,name in zip(paths,names)]
need(paths[1:]==rank['lean_path'].split(':') and all(sha(p)==r[k] for p,k in zip(objects,keys)) and r[keys[0]]==rank['object_sha256'] and all(r[k]==rank[k] for k in keys[1:]),'provider mismatch')
need(len(r['samples'])==3 and all(x['mem_available_kib']>=8*1024**2 and len(x['lean'])<=2 for x in [r['preflight']]+r['samples']),'resource record mismatch')
prior=subprocess.run([sys.executable,'-I','-S','-B',str(D/'reviews/ordinary12-direct-main-rank-independent/check.py')],capture_output=True,check=True);need(not prior.stderr and json.loads(prior.stdout)['status']=='PASS','rank/provider review failed')
checkpins();need(sha(out)==r['object_sha256'] and all(sha(p)==r[k] for p,k in zip(objects,keys)),'proof object changed')
print(json.dumps({'status':'PASS','positive_beta_witnesses_graph_zero_and_explicit_window_required':True,'conditional_index_congruence':'2*n mod q^4 = R+1','n_lower_bound':13,'selected_producers_match':12,'rank_and_1291_union_review':'PASS','scope':'conditional model-level early index; no exact alignment, halt or iPRA proof'},indent=2))
