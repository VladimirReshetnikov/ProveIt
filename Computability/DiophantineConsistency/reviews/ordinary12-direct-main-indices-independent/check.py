#!/usr/bin/env python3
"""Read-only review of positive graph-to-Pell-indices join."""
from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
if sys.flags.optimize:raise SystemExit('optimized Python refused')
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary12-direct-main-probe';O=P/'observations/indices-attempt03'; A=P/'observations/oriented-attempt02/terminal.json';L=P/'observations/pell-attempt01/terminal.json';N=P/'observations/norm-attempt01/terminal.json';J=P/'observations/attempt01/terminal.json';B=D/'research/ordinary12-qcube92-candidate/observations/halt2-attempt01/terminal.json'
pins={P/'INDICES.md':'e8dc4fab596a8c05b93896f3852ee0a80f89510e2cc8d74ca217925f9db02766',P/'DirectMainIndices.lean':'a9e40ed1b19a6eda1973ed8dfa6f045bd47c415251be11348d42bf7f69d2267f',P/'run-indices.py':'b03f8ba96de1b33957660ba94d8a244aab1dc5ff4c4bd5a3c172449bfb9b7751',O/'terminal.json':'d03cf9f90629a488bc08fff66d75eed0165d0a79d444192f790d0a0491bd0ad6',O/'stdout':'96fb4606cf0073816f15fa54e386368a0c46157746d69124a3d0a05641d7d192',A:'03b3137c0763f25f59edcb375c7f01f795c1ad9f35ac8512dfd8c4e6156b308e',L:'58b40dd17a5f18c81c018442afeebc9aa3d2f673d77953cecaee5987aaa23b33',N:'e6303bca05e8304068a8efda87c9ec2ab763bc558a1476158faeb5267aabaf12',J:'2bf0934017209ddb4fab587740a9e680e80ce0f878f490856f5928e9fb66c81e',B:'8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f'}
def need(v,m):
 if not v:raise SystemExit(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def checkpins():
 for p,h in pins.items():need(sha(p)==h,'pin mismatch '+str(p))
checkpins();s=(P/'DirectMainIndices.lean').read_text();r=json.loads((O/'terminal.json').read_text());a=json.loads(A.read_text());l=json.loads(L.read_text());n=json.loads(N.read_text());j=json.loads(J.read_text())
need(s.splitlines()[:2]==['import DirectMainOriented','import DirectMainPell'] and 'variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in s,'model/import mismatch')
h=s.split('theorem graph_indices',1)[1].split(':= by',1)[0]
for x in ('(p : Fin 4 → ℕ) (v : Fin 12 → V)','(hb : 0<(p 0:V)) (hv : ∀j,0<v j)','(hz : InternalZero (graph (DirectMainFirst.integerPorts p)).output v)','let b : V := v 0*(p 0:V)','let q : V := 1+b','let X : V := q*v 5','let Y : V := (q*(q*q))*v 6','let U : V := Y*(q*q)','let k : V := v 8+v 9','let c : V := v 8+Y*k','let a : V := X*Y+Y','let H : V := 3+4*a','let R : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)','let P : V := U*(X+a*c)+H*(U*v 11+R+1)','let N : V := H*k','let Q : V := (X*Y)*Y','∃ first main n m : V, 0<first ∧ 0<main ∧ P=N+U*main ∧','0<n ∧ 0<m ∧ n≤k ∧ m≤c ∧','xcoord n (2*(Q-1)+1)=first ∧ 2*ycoord n (2*(Q-1)+1)=k ∧','xcoord m a=main ∧ ycoord m a=c'):need(x in h,'theorem mismatch '+x)
for x in ('have hq2 : 2≤q','have hY : 8≤Y','have hX : 0<X','have hU : 0<U','have hk : 0<k','DirectMainFirstQuotient.first_root p v hz hb0','DirectMainOriented.direct_norm p v hb hv hz','DirectMainPell.direct_indices U X Y k (v 8) (v 11) R first hU hX hY hk (hv 8) hfirst hmain'):need(x in s,'proof join mismatch '+x)
need('set_option linter.' not in s,'unexpected local lint suppression')
need(r['exit']==0 and r['reason'] is None and r['union_unchanged'] and r['union_count']==1291 and r['base_receipt_sha256']==sha(B),'receipt failure')
need(r['source_sha256']==r['source_after']==sha(P/'DirectMainIndices.lean')==sha(O/'source.txt') and r['runner_sha256']==r['runner_after']==sha(P/'run-indices.py'),'source/runner mismatch')
need(r['lean_sha256']==r['lean_after']==sha(r['command'][0]) and r['stdout_sha256']==sha(O/'stdout') and r['stderr_sha256']==sha(O/'stderr') and not (O/'stderr').read_bytes(),'Lean/log mismatch')
need((O/'stdout').read_text()=="'DirectMainIndices.graph_indices' depends on axioms: [propext, Classical.choice, Quot.sound]\n",'axiom report mismatch')
out=Path(r['command'][r['command'].index('-o')+1]);src=Path(r['command'][r['command'].index('-o')-1]);need(sha(out)==r['object_sha256']=='9b2e4a71257e9a6b2b151103eccdf78564a9c912e79a8a3c5113d87beb429941' and sha(src)==sha(P/'DirectMainIndices.lean'),'compiled object mismatch')
paths=r['lean_path'].split(':');names=('DirectMainOriented','DirectMainPell','DirectMainNorm','DirectMainProjection','DirectMainMain','DirectMainTransport','DirectMainFirstQuotient','DirectMainFirst','DirectMainGraph','XQ91');keys=('oriented_producer_sha256','pell_producer_sha256','norm_producer_sha256','projection_producer_sha256','main_producer_sha256','transport_producer_sha256','quotient_producer_sha256','first_producer_sha256','graph_producer_sha256','xq91_producer_sha256');objects=[Path(p)/(name+'.olean') for p,name in zip(paths,names)]
need(paths[4:]==a['lean_path'].split(':') and all(sha(p)==r[k] for p,k in zip(objects,keys)) and r[keys[0]]==a['object_sha256'] and r[keys[1]]==l['object_sha256'] and r[keys[2]]==n['object_sha256'] and r[keys[3]]==j['object_sha256'] and all(r[k]==a[k] for k in keys[4:]),'provider mismatch')
need(len(r['samples'])==2 and all(x['mem_available_kib']>=8*1024**2 and len(x['lean'])<=2 for x in [r['preflight']]+r['samples']),'resource record mismatch')
for i in ('01','02'):
 f=P/('observations/indices-attempt'+i);z=json.loads((f/'terminal.json').read_text());log=(f/'stdout').read_text();need(z['exit']!=0 and z['object_sha256'] is None and sha(f/'source.txt')==z['source_sha256'] and sha(f/'stdout')==z['stdout_sha256'] and sha(f/'stderr')==z['stderr_sha256'] and 'error:' in log and 'sorryAx' in log,'failed attempt mismatch '+i)
for review in ('ordinary12-direct-main-oriented-independent','ordinary12-direct-main-pell-independent'):
 prior=subprocess.run([sys.executable,'-I','-S','-B',str(D/'reviews'/review/'check.py')],capture_output=True,check=True);need(not prior.stderr and json.loads(prior.stdout)['status']=='PASS','prior review failed '+review)
checkpins();need(sha(out)==r['object_sha256'] and all(sha(p)==r[k] for p,k in zip(objects,keys)),'proof object changed')
print(json.dumps({'status':'PASS','beta_witness_positivity_and_graph_zero_required':True,'four_positive_values_and_coordinate_equations':True,'ten_selected_producers_match':True,'failed_attempts':['01','02'],'accepted_attempt':'03','oriented_pell_and_1291_union_reviews':'PASS','scope':'model-level graph-to-indices; no index alignment, halt equivalence or iPRA proof'},indent=2))
