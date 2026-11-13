#!/usr/bin/env python3
"""Read-only review of conditional direct-main projection and norm builds."""
from hashlib import sha256
import json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary12-direct-main-probe';B=D/'research/ordinary12-qcube92-candidate/observations/halt2-attempt01/terminal.json';O=P/'observations/attempt01';N=P/'observations/norm-attempt01'
PIN={P/'README.md':'1f471c717a4767ff71d49cdbcf39cd8d613a2c06b8c5f5e129363135e50b71dd',
 P/'NORM.md':'c8625f6c1db54a5b6400e5083678ef4db59cc83797a0ea4e0b7fcdd944e04173',
 P/'DirectMainProjection.lean':'913b54cea53402e9da91b2fb9e5c41dbbf9e5926be9531986fc08fe90163a956',
 P/'DirectMainNorm.lean':'738c9a708950bca11bccb1904fe9d79192f85939f76c9bab6a0a549f3af74400',
 P/'run.py':'cdc0b0610c1bd49dcd442f3741cd83f95caf34d7e9a9844865acb87dbc788b66',
 P/'run-norm.py':'7e4380e9c0e8a508787db4a017ebacfe72019c8288a1521c9a7dd75d858fc611',
 O/'terminal.json':'2bf0934017209ddb4fab587740a9e680e80ce0f878f490856f5928e9fb66c81e',
 O/'source.txt':'913b54cea53402e9da91b2fb9e5c41dbbf9e5926be9531986fc08fe90163a956',
 O/'stdout':'bc9ff1b95cea4413d53e26ef5bb4fb71131ca6748cc8cdc3d5175b60c4f15a2f',
 N/'terminal.json':'e6303bca05e8304068a8efda87c9ec2ab763bc558a1476158faeb5267aabaf12',
 N/'source.txt':'738c9a708950bca11bccb1904fe9d79192f85939f76c9bab6a0a549f3af74400',
 N/'stdout':'c2751e1109bbfc941aa7456f6ae2bd192418f58fb7646c8b5584e611b5aba296',
 B:'8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f'}
def need(x,m):
 if not x:raise SystemExit(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
for p,h in PIN.items():need(sha(p)==h,'input mismatch '+str(p))
s=(P/'DirectMainProjection.lean').read_text();n=(P/'DirectMainNorm.lean').read_text();p=json.loads((O/'terminal.json').read_text());q=json.loads((N/'terminal.json').read_text());base=json.loads(B.read_text())
need(s.splitlines()[0]=='import DiophantineConsistency.ArithmeticAdaptiveMainOrientation2011' and n.splitlines()[0]=='import DirectMainProjection','direct imports mismatch')
for source in (s,n):need('variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in source,'model assumptions')
for fragment in ('theorem direct_parts_positive (U X Y k eta G R : V)',
 '(hU : 0 < U) (hY : 8 ≤ Y) (hk : 0 < k)',
 'H*k < U*(X+a*c)+H*(U*G+R+1)',
 'theorem cancel_direct_root (U X a c H G R W main : V) (hU : 0<U)',
 '(hroot : U*(X+a*c)+H*(U*G+R+1) = H*(R+1+U*W)+U*main)',
 'X+a*c+H*G = main+H*W',
 '(hU : 0<U) (hH : 0<H) (hX : X<H) (hP : P<H)',
 '(hproj : main=P+a*c+H*t) : X=P'):
 need(fragment in s,'projection hypothesis/conclusion mismatch '+fragment)
for fragment in ('theorem oriented_scaled_norm (U P N C : V) (hU : 0<U) (hPN : N<P)',
 '(hnorm : magnitude (P,N)*magnitude (P,N)=U*U*(1+C))',
 '∃ m : V, 0<m ∧ P=N+U*m ∧ m*m=1+C',
 'theorem direct_main_orientation (U X Y k eta G R : V)',
 '(hU : 0<U) (hY : 8≤Y) (hk : 0<k)',
 'magnitude (P,N)*magnitude (P,N)=U*U*(1+(H+a*a)*(c*c))',
 '∃ m : V, 0<m ∧ P=N+U*m ∧ m*m=1+(H+a*a)*(c*c)'):
 need(fragment in n,'norm hypothesis/conclusion mismatch '+fragment)
# This arbitrary-natural counterexample satisfies every direct_projection
# hypothesis except X<H, and has X != P. It is not claimed to be graph-derived.
U,X,a,c,H,G,R,W,main,Pval,t=1,3,0,0,2,1,0,1,3,1,1
need(U>0 and H>0 and Pval<H and not X<H and X!=Pval,'counterexample bounds')
need(U*(X+a*c)+H*(U*G+R+1)==H*(R+1+U*W)+U*main and main==Pval+a*c+H*t,'counterexample balance/projection')
for receipt,folder,source,runner,names,minimum in [
 (p,O,'DirectMainProjection.lean','run.py',['direct_parts_positive','cancel_direct_root','direct_projection'],18508148),
 (q,N,'DirectMainNorm.lean','run-norm.py',['oriented_scaled_norm','direct_main_orientation'],18527976)]:
 need(receipt['exit']==0 and receipt['reason'] is None and receipt['union_unchanged'] and receipt['union_count']==1291,'author run failed')
 need(receipt['source_sha256']==receipt['source_after']==sha(P/source)==sha(folder/'source.txt'),'source mismatch')
 need(receipt['runner_sha256']==receipt['runner_after']==sha(P/runner),'runner mismatch')
 lean=Path(receipt['command'][0]);need(receipt['lean_sha256']==receipt['lean_after']==sha(lean),'Lean binary mismatch')
 need(receipt['base_receipt_sha256']==sha(B),'base receipt mismatch')
 out=Path(receipt['command'][receipt['command'].index('-o')+1]);copy=Path(receipt['command'][receipt['command'].index('-o')-1])
 need(sha(out)==receipt['object_sha256'] and sha(copy)==sha(P/source),'compiled object/source mismatch')
 prefix='DirectMainProjection' if folder==O else 'DirectMainNorm'
 expected=''.join("'"+prefix+'.'+name+"' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for name in names)
 need((folder/'stdout').read_text()==expected and not (folder/'stderr').read_bytes() and sha(folder/'stdout')==receipt['stdout_sha256'] and sha(folder/'stderr')==receipt['stderr_sha256'],'log mismatch')
 need(len(receipt['samples'])==2 and min(x['mem_available_kib'] for x in receipt['samples'])==minimum and max(len(x['lean']) for x in receipt['samples'])==1,'resource observation mismatch')
need(q['projection_producer_sha256']==p['object_sha256']=='e2510b3deeebc7d4067710ad1f3210191e6189050a9b3bfa8641f9a9a2bf3182','projection producer mismatch')
proot=Path(p['output_root']);paths=q['lean_path'].split(':');need(Path(paths[0])==proot and sha(proot/'DirectMainProjection.olean')==p['object_sha256'],'norm import resolution mismatch')
need(p['lean_path'].split(':')==paths[1:],'base provider order mismatch');lib=Path(paths[1])
def verify_union():
 actual={x.relative_to(lib).as_posix():x for x in lib.rglob('*') if x.is_file()}
 need(set(actual)==set(base['union']) and len(actual)==1291,'selected union membership')
 for rel,x in actual.items():
  z=base['union'][rel];need(x.is_symlink() and os.readlink(x)==z['link'] and str(x.resolve())==z['resolved'] and sha(x)==z['sha256'],'selected union drift '+rel)
verify_union()
source_module='DiophantineConsistency/ArithmeticAdaptiveMainOrientation2011.olean';need(source_module in base['union'],'missing direct projection dependency')
prior=subprocess.run([sys.executable,'-I','-S','-B',str(D/'reviews/ordinary12-qcube92-halt-independent/check.py')],capture_output=True,check=True)
need(not prior.stderr and json.loads(prior.stdout)['halt_attempt_exit']==0,'prior 92 provider review failed')
verify_union()
for path,h in PIN.items():need(sha(path)==h,'input changed during review '+str(path))
for receipt in (p,q):need(sha(Path(receipt['output_root'])/(('DirectMainProjection' if receipt is p else 'DirectMainNorm')+'.olean'))==receipt['object_sha256'],'object changed during review')
print(json.dumps({'status':'PASS','projection_lemmas':3,'norm_lemmas':2,'both_author_exits':0,
 'selected_union_objects':len(base['union']),'projection_object_matches_norm_import':True,
 'abstract_counterexample_without_X_bound':True,'scope':'conditional model lemmas; no 90-graph or iPRA theorem'},indent=2))
