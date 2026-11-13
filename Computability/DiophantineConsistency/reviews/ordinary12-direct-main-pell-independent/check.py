#!/usr/bin/env python3
"""Read-only audit of conditional Pell classification and recorded provider."""
from hashlib import sha256
import json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary12-direct-main-probe';O=P/'observations/pell-attempt01'
N=P/'observations/norm-attempt01/terminal.json';J=P/'observations/attempt01/terminal.json'
B=D/'research/ordinary12-qcube92-candidate/observations/halt2-attempt01/terminal.json'
OLD=D/'research/ordinary12-ipra-bridge/free-j-pell-indices-prototype/FreeJPellIndices.lean'
DELTA=D/'Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean'
PIN={P/'PELL.md':'ad5770393f7051f85e8ef598333ef31313b48bbb5d82d3d4123df117caf426eb',
 P/'DirectMainPell.lean':'d50655779bf10d08b7b2586085141d35faea6fa5473075cec04a2146e4f67bb5',
 P/'run-pell.py':'f2cbce81c26bd040f4c4a52b63ae309e5ceb49bced8d55f2e70810bcb611c575',
 O/'terminal.json':'58b40dd17a5f18c81c018442afeebc9aa3d2f673d77953cecaee5987aaa23b33',
 O/'source.txt':'d50655779bf10d08b7b2586085141d35faea6fa5473075cec04a2146e4f67bb5',
 O/'stdout':'7e7653a56daeef74473cbb49aaf4a0b6a6cdb4303b4b4692af483d02661a862b',
 N:'e6303bca05e8304068a8efda87c9ec2ab763bc558a1476158faeb5267aabaf12',
 J:'2bf0934017209ddb4fab587740a9e680e80ce0f878f490856f5928e9fb66c81e',
 B:'8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f',
 OLD:'8d222d5302d22c914694dbe36478870af9358b0a26046a8135a0b26c1ac4bf72',
 DELTA:'63ec2a49f8d7066dbd8647a663db4bbd7255abd3ca7c3cc0d4d7b3533a189b16'}
def need(v,m):
 if not v:raise SystemExit(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
for p,h in PIN.items():need(sha(p)==h,'input mismatch '+str(p))
s=(P/'DirectMainPell.lean').read_text();o=OLD.read_text();delta=DELTA.read_text();r=json.loads((O/'terminal.json').read_text());nr=json.loads(N.read_text());pr=json.loads(J.read_text());base=json.loads(B.read_text())
need(s.splitlines()[:2]==['import DirectMainNorm','import DiophantineConsistency.ArithmeticAdaptivePellIndices2011'],'direct imports mismatch')
need('variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in s,'model hypothesis mismatch')
first=s.split('theorem indices_of_norms',1)[1].split(':= by',1)[0]
for fragment in ('(Q k a c first main : V)','(hQ : 0<Q) (hk : 0<k) (hc : 0<c)',
 '(hn : first*first=1+Q*(Q+1)*k*k)','(hm : main*main=1+delta a*c*c)',
 '∃ n m : V, 0<n ∧ 0<m ∧ n≤k ∧ m≤c ∧',
 'xcoord n (2*(Q-1)+1)=first ∧ 2*ycoord n (2*(Q-1)+1)=k ∧',
 'xcoord m a=main ∧ ycoord m a=c'):
 need(fragment in first,'first theorem hypothesis/conclusion mismatch '+fragment)
second=s.split('theorem direct_indices',1)[1].split(':= by',1)[0]
for fragment in ('(U X Y k eta G R first : V)','(hU : 0<U) (hX : 0<X) (hY : 8≤Y) (hk : 0<k) (heta : 0<eta)',
 '(hfirst : first*first=1+((X*Y)*Y)*(((X*Y)*Y)+1)*k*k)',
 'magnitude (P,N)*magnitude (P,N)=U*U*(1+(H+a*a)*(c*c))',
 '∃ main n m : V, 0<main ∧ P=N+U*main ∧ 0<n ∧ 0<m ∧ n≤k ∧ m≤c ∧',
 'xcoord n (2*(Q-1)+1)=first ∧ 2*ycoord n (2*(Q-1)+1)=k ∧',
 'xcoord m a=main ∧ ycoord m a=c'):
 need(fragment in second,'direct theorem hypothesis/conclusion mismatch '+fragment)
need('0<first' not in first and '0<first' not in second,'first positivity unexpectedly asserted')
need('direct_main_orientation U X Y k eta G R hU hY hk hnorm' in s and 'indices_of_norms Q k a c first main' in s,'expected proof composition missing')
need('def delta (b : V) : V := (b+1)*(b+3)' in delta,'delta source changed')
need('theorem indices (p : Fin 4 → ℕ) (v : Fin 12 → V)' in o and '(hz : InternalZero (literal (fun j => (p j:ℤ))) v)' in o,'old graph-zero theorem changed')
need('0<first ∧ 0<main' in o and 'magnitude (pairEval (core (fun j => (p j:ℤ))).z v)=M*first' in o and 'Equivalent (pairEval (core (fun j => (p j:ℤ))).d v) (natural (U*main))' in o,'old signed-pair conclusions changed')
# Exact coefficient comparison for (3+4a)+a²=(a+1)(a+3).
left={0:3,1:4,2:1};right={0:3,1:1+3,2:1};need(left==right,'delta identity failed')
need(r['exit']==0 and r['reason'] is None and r['union_unchanged'] and r['union_count']==1291,'author receipt failed')
need(r['source_sha256']==r['source_after']==sha(P/'DirectMainPell.lean')==sha(O/'source.txt'),'source mismatch')
need(r['runner_sha256']==r['runner_after']==sha(P/'run-pell.py'),'runner mismatch')
lean=Path(r['command'][0]);need(r['lean_sha256']==r['lean_after']==sha(lean),'Lean binary mismatch')
need(r['base_receipt_sha256']==sha(B) and base['exit']==0 and base['union_unchanged'],'base receipt mismatch')
expected="'DirectMainPell.indices_of_norms' depends on axioms: [propext, Classical.choice, Quot.sound]\n'DirectMainPell.direct_indices' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
need((O/'stdout').read_text()==expected and not (O/'stderr').read_bytes() and sha(O/'stdout')==r['stdout_sha256'] and sha(O/'stderr')==r['stderr_sha256'],'Lean log mismatch')
out=Path(r['command'][r['command'].index('-o')+1]);compiled=Path(r['command'][r['command'].index('-o')-1])
need(sha(out)==r['object_sha256']=='753c3774163dd16a835157cdccc71ee05f81ad81bb45ec9eaf2d612cc7710f97' and sha(compiled)==sha(P/'DirectMainPell.lean'),'compiled source/object mismatch')
need(len(r['samples'])==2 and min(x['mem_available_kib'] for x in r['samples'])==18455552 and max(len(x['lean']) for x in r['samples'])==1,'resource sample mismatch')
need(all(x['exit']==0 and x['reason'] is None and x['union_unchanged'] for x in (nr,pr)),'prior producer receipt failed')
norm=Path(nr['output_root'])/'DirectMainNorm.olean';projection=Path(pr['output_root'])/'DirectMainProjection.olean';paths=r['lean_path'].split(':')
need(Path(paths[0])==norm.parent and Path(paths[1])==projection.parent and sha(norm)==r['norm_producer_sha256']==nr['object_sha256'] and sha(projection)==r['projection_producer_sha256']==pr['object_sha256'],'norm/projection producer mismatch')
lib=Path(paths[2]);need(paths[2:]==pr['lean_path'].split(':'),'base provider order differs')
need('DiophantineConsistency/ArithmeticAdaptivePellIndices2011.olean' in base['union'],'Pell index object absent')
def verify_union():
 actual={x.relative_to(lib).as_posix():x for x in lib.rglob('*') if x.is_file()};need(set(actual)==set(base['union']) and len(actual)==1291,'union membership drift')
 for rel,x in actual.items():
  v=base['union'][rel];need(x.is_symlink() and os.readlink(x)==v['link'] and str(x.resolve())==v['resolved'] and sha(x)==v['sha256'],'union object drift '+rel)
verify_union()
prior=subprocess.run([sys.executable,'-I','-S','-B',str(D/'reviews/ordinary12-direct-main-independent/check.py')],capture_output=True,check=True)
need(not prior.stderr and json.loads(prior.stdout)['status']=='PASS','prior projection/norm review failed')
verify_union()
for p,h in PIN.items():need(sha(p)==h,'input changed during review '+str(p))
need(sha(out)==r['object_sha256'] and sha(norm)==r['norm_producer_sha256'] and sha(projection)==r['projection_producer_sha256'],'proof object changed')
print(json.dumps({'status':'PASS','conditional_pell_lemmas':2,'author_exit':r['exit'],
 'selected_union_objects':1291,'norm_and_projection_objects_match':True,
 'old_graph_link_and_first_positivity_not_claimed':True,
 'scope':'conditional model classification, no graph or iPRA equivalence'},indent=2))
