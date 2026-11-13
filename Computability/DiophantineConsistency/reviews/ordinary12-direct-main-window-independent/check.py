#!/usr/bin/env python3
"""Read-only review of direct-draft radix window and early-index join."""
from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
if sys.flags.optimize:raise SystemExit('optimized Python refused')
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary12-direct-main-probe';O=P/'observations/window-attempt02';F=P/'observations/window-attempt01';E=P/'observations/early-attempt01/terminal.json';B=D/'research/ordinary12-qcube92-candidate/observations/halt2-attempt01/terminal.json'
pins={P/'WINDOW.md':'4a8b089275a67c38f3a66ef157ff397076a94fe1f6d5ef08552fedb1897757ff',P/'DirectMainWindow.lean':'ccf1f1fed2c0774ed9b255c0f7d849adbb8ed931f75bb3f58952c750a5609671',P/'run-window.py':'1e276cc055f80922194960c3f80100b735f78d986c75fc85b320d8fe9451b9f7',O/'terminal.json':'35da03939095fb4289c1a1c1bed5cdaf0d36eb452590f5c3693f4a92277cb461',O/'stdout':'453c878e4e44bb08a9f2fce0c183964021d07183292bcd89c52671cb8d81fc3a',F/'terminal.json':'231e94e54a3cbdf1670e9b5b79b3a8084b9ab4e5a078bb7e2229de819269f51a',F/'source.txt':'6a0bd59c7dcea0bf168d5c21c0fcf592c9e5f34412cef0566496908ade94326a',F/'stdout':'741397497ca90716e7e4c3a74decb84ed6e34f5fa739258f9d3335712316b3c1',E:'0507db7193667baf529fc62bf1f80063530296516e668f61e68670e0b305d357',B:'8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f'}
def need(v,m):
 if not v:raise SystemExit(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def checkpins():
 for p,h in pins.items():need(sha(p)==h,'pin mismatch '+str(p))
checkpins();s=(P/'DirectMainWindow.lean').read_text();r=json.loads((O/'terminal.json').read_text());f=json.loads((F/'terminal.json').read_text());e=json.loads(E.read_text())
need(s.splitlines()[:2]==['import DirectMainEarly','import DiophantineConsistency.ArithmeticAdaptiveRankWindow2011'] and 'variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in s,'model/import mismatch')
a=s.split('theorem graph_window',1)[1].split(':= by',1)[0];h=s.split('theorem graph_early',1)[1].split(':= by',1)[0]
for part in (a,h):
 for x in ('(p : Fin 4 → ℕ) (v : Fin 12 → V)','(hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))','(hv : ∀j,0<v j) (hz : InternalZero (graph (DirectMainFirst.integerPorts p)).output v)','let b : V := v 0*(p 0:V)','let q : V := 1+b','let R : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)'):need(x in part,'hypothesis mismatch '+x)
need('24≤R ∧ R+q^3+q+1≤q^4' in a,'window mismatch')
for x in ('let X : V := q*v 5','let Y : V := (q*(q*q))*v 6','let k : V := v 8+v 9','let c : V := v 8+Y*k','let a : V := X*Y+Y','let Q : V := (X*Y)*Y','∃ first main n m : V, 0<first ∧ 0<main ∧ 13≤n ∧ 0<m ∧ n≤k ∧ m≤c ∧','xcoord n (2*(Q-1)+1)=first ∧ 2*ycoord n (2*(Q-1)+1)=k ∧','xcoord m a=main ∧ ycoord m a=c ∧ (2*n)%(q^4)=R+1 ∧ R+1≤2*n ∧ R+1≤k'):need(x in h,'early conclusion mismatch '+x)
for x in ('DirectMainTransport.transport p v hb hv hz','scalar_rank_window q','hb (hv 0) (hv 1) (hv 2) hl hh hq hgap','DirectMainEarly.early_of_window p v hb hv hz (graph_window p v hb hl hh hv hz)'):need(x in s,'proof linkage mismatch '+x)
need('set_option linter.' not in s,'unexpected local lint suppression')
need(r['exit']==0 and r['reason'] is None and r['union_unchanged'] and r['union_count']==1291 and r['base_receipt_sha256']==sha(B),'receipt failure')
need(r['source_sha256']==r['source_after']==sha(P/'DirectMainWindow.lean')==sha(O/'source.txt') and r['runner_sha256']==r['runner_after']==sha(P/'run-window.py'),'source/runner mismatch')
need(r['lean_sha256']==r['lean_after']==sha(r['command'][0]) and r['stdout_sha256']==sha(O/'stdout') and r['stderr_sha256']==sha(O/'stderr') and not (O/'stderr').read_bytes(),'Lean/log mismatch')
expected=''.join(f"'DirectMainWindow.{name}' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for name in ('graph_window','graph_early'))
need((O/'stdout').read_text()==expected,'axiom report mismatch')
need(f['exit']==0 and f['reason'] is None and f['object_sha256'] is not None and sha(F/'source.txt')==f['source_sha256'] and sha(F/'stdout')==f['stdout_sha256'] and sha(F/'stderr')==f['stderr_sha256'] and 'The `ring` tactic failed' in (F/'stdout').read_text() and 'sorryAx' not in (F/'stdout').read_text() and (F/'stdout').read_text().endswith(expected),'first observation mismatch')
out=Path(r['command'][r['command'].index('-o')+1]);src=Path(r['command'][r['command'].index('-o')-1]);need(sha(out)==r['object_sha256']=='cecce5dabc8fb031bf8dee1c463be198cb9a91442384eb555d5b190a786bb5db' and sha(src)==sha(P/'DirectMainWindow.lean'),'compiled object mismatch')
paths=r['lean_path'].split(':');names=('DirectMainEarly','DirectMainRank','DirectMainIndices','DirectMainOriented','DirectMainPell','DirectMainNorm','DirectMainProjection','DirectMainMain','DirectMainTransport','DirectMainFirstQuotient','DirectMainFirst','DirectMainGraph','XQ91');keys=('early_producer_sha256','rank_producer_sha256','indices_producer_sha256','oriented_producer_sha256','pell_producer_sha256','norm_producer_sha256','projection_producer_sha256','main_producer_sha256','transport_producer_sha256','quotient_producer_sha256','first_producer_sha256','graph_producer_sha256','xq91_producer_sha256');objects=[Path(p)/(name+'.olean') for p,name in zip(paths,names)]
need(paths[1:]==e['lean_path'].split(':') and all(sha(p)==r[k] for p,k in zip(objects,keys)) and r[keys[0]]==e['object_sha256'] and all(r[k]==e[k] for k in keys[1:]),'provider mismatch')
need(len(r['samples'])==3 and all(x['mem_available_kib']>=8*1024**2 and len(x['lean'])<=2 for x in [r['preflight']]+r['samples']),'resource record mismatch')
prior=subprocess.run([sys.executable,'-I','-S','-B',str(D/'reviews/ordinary12-direct-main-early-independent/check.py')],capture_output=True,check=True);need(not prior.stderr and json.loads(prior.stdout)['status']=='PASS','early/provider review failed')
checkpins();need(sha(out)==r['object_sha256'] and all(sha(p)==r[k] for p,k in zip(objects,keys)),'proof object changed')
print(json.dumps({'status':'PASS','required_ports':'0<beta, MC<beta, MF<2*beta','draft_zero_and_positive_witnesses_required':True,'explicit_window_discharged':True,'first_attempt':'exit 0 with nonfatal tactic diagnostic','accepted_attempt':'02','selected_producers_match':13,'early_and_1291_union_review':'PASS','scope':'bounded-port model-level early index; no exact alignment, halt or iPRA proof'},indent=2))
