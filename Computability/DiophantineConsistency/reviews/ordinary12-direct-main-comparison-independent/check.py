#!/usr/bin/env python3
"""Read-only review of bounded-port Pell index comparison."""
from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
if sys.flags.optimize:raise SystemExit('optimized Python refused')
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary12-direct-main-probe';O=P/'observations/comparison-attempt01';W=P/'observations/window-attempt02/terminal.json';B=D/'research/ordinary12-qcube92-candidate/observations/halt2-attempt01/terminal.json'
pins={P/'COMPARISON.md':'196dd6a85885dfa6f3d4ebf68915a6e4c2f2e971b5af190167068ddb2967ba15',P/'DirectMainComparison.lean':'36bba26b975a3e571cdb1668070dd25eacdd2360491231f539a2e02712516119',P/'run-comparison.py':'c4677a603c6834051c983d8d2bc90775e6a532caac8d192b4b923bc56687c1ea',O/'terminal.json':'45f0c78941872748fd8ae3afe869673dcdcc10846776e6150755bc8f0598d6bf',O/'stdout':'c8f746d947bea84cbff1eaf138ad0d096ab95824f73c708000be8d2daae9ac7e',W:'35da03939095fb4289c1a1c1bed5cdaf0d36eb452590f5c3693f4a92277cb461',B:'8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f'}
def need(v,m):
 if not v:raise SystemExit(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def checkpins():
 for p,h in pins.items():need(sha(p)==h,'pin mismatch '+str(p))
checkpins();s=(P/'DirectMainComparison.lean').read_text();r=json.loads((O/'terminal.json').read_text());w=json.loads(W.read_text())
need(s.splitlines()[:2]==['import DirectMainWindow','import DiophantineConsistency.ArithmeticAdaptiveIndexComparison2011'] and 'variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in s,'model/import mismatch')
h=s.split('theorem comparison',1)[1].split(':= by',1)[0]
for x in ('(p : Fin 4 → ℕ) (v : Fin 12 → V)','(hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))','(hv : ∀j,0<v j) (hz : InternalZero (graph (DirectMainFirst.integerPorts p)).output v)','let b : V := v 0*(p 0:V)','let q : V := 1+b','let X : V := q*v 5','let Y : V := (q*(q*q))*v 6','let k : V := v 8+v 9','let c : V := v 8+Y*k','let a : V := X*Y+Y','let Q : V := (X*Y)*Y','let R : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)','∃ first main n m : V, 0<first ∧ 0<main ∧ 13≤n ∧ n<m ∧ 14≤m ∧ 2*R<c ∧ n≤k ∧ m≤c ∧','xcoord n (2*(Q-1)+1)=first ∧ 2*ycoord n (2*(Q-1)+1)=k ∧','xcoord m a=main ∧ ycoord m a=c ∧ (2*n)%(q^4)=R+1 ∧ R+1≤2*n ∧ R+1≤k'):need(x in h,'theorem mismatch '+x)
for x in ('DirectMainWindow.graph_early p v hb hl hh hv hz','two_le_of_positive_cube_quotient','(y_strictMono a).monotone hm\'','(base_mono a B hab n).2','have hhalf : 2*R<c'):need(x in s,'proof linkage mismatch '+x)
need('set_option linter.' not in s,'unexpected local lint suppression')
need(r['exit']==0 and r['reason'] is None and r['union_unchanged'] and r['union_count']==1291 and r['base_receipt_sha256']==sha(B),'receipt failure')
need(r['source_sha256']==r['source_after']==sha(P/'DirectMainComparison.lean')==sha(O/'source.txt') and r['runner_sha256']==r['runner_after']==sha(P/'run-comparison.py'),'source/runner mismatch')
need(r['lean_sha256']==r['lean_after']==sha(r['command'][0]) and r['stdout_sha256']==sha(O/'stdout') and r['stderr_sha256']==sha(O/'stderr') and not (O/'stderr').read_bytes(),'Lean/log mismatch')
need((O/'stdout').read_text()=="'DirectMainComparison.comparison' depends on axioms: [propext, Classical.choice, Quot.sound]\n",'axiom report mismatch')
out=Path(r['command'][r['command'].index('-o')+1]);src=Path(r['command'][r['command'].index('-o')-1]);need(sha(out)==r['object_sha256']=='42d86b41387d230d85b9de33b0eca8c7b340975e15fab6d9c0be9086c305263d' and sha(src)==sha(P/'DirectMainComparison.lean'),'compiled object mismatch')
paths=r['lean_path'].split(':');names=('DirectMainWindow','DirectMainEarly','DirectMainRank','DirectMainIndices','DirectMainOriented','DirectMainPell','DirectMainNorm','DirectMainProjection','DirectMainMain','DirectMainTransport','DirectMainFirstQuotient','DirectMainFirst','DirectMainGraph','XQ91');keys=('window_producer_sha256','early_producer_sha256','rank_producer_sha256','indices_producer_sha256','oriented_producer_sha256','pell_producer_sha256','norm_producer_sha256','projection_producer_sha256','main_producer_sha256','transport_producer_sha256','quotient_producer_sha256','first_producer_sha256','graph_producer_sha256','xq91_producer_sha256');objects=[Path(p)/(name+'.olean') for p,name in zip(paths,names)]
need(paths[1:]==w['lean_path'].split(':') and all(sha(p)==r[k] for p,k in zip(objects,keys)) and r[keys[0]]==w['object_sha256'] and all(r[k]==w[k] for k in keys[1:]),'provider mismatch')
need(len(r['samples'])==3 and all(x['mem_available_kib']>=8*1024**2 and len(x['lean'])<=2 for x in [r['preflight']]+r['samples']),'resource record mismatch')
prior=subprocess.run([sys.executable,'-I','-S','-B',str(D/'reviews/ordinary12-direct-main-window-independent/check.py')],capture_output=True,check=True);need(not prior.stderr and json.loads(prior.stdout)['status']=='PASS','window/provider review failed')
checkpins();need(sha(out)==r['object_sha256'] and all(sha(p)==r[k] for p,k in zip(objects,keys)),'proof object changed')
print(json.dumps({'status':'PASS','required_ports':'0<beta, MC<beta, MF<2*beta','draft_zero_and_positive_witnesses_required':True,'index_order':'13<=n<m and 14<=m','extra_bound':'2*R<c','selected_producers_match':14,'window_and_1291_union_review':'PASS','scope':'bounded-port model-level comparison; no exact alignment, halt or iPRA proof'},indent=2))
