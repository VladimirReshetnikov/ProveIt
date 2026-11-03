#!/usr/bin/env python3
"""Read-only independent audit of fixed-port 91-gate model halt result."""
from hashlib import sha256
import json,os,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary12-xq91-candidate';O=P/'observations/halt-attempt04'
BASE=D/'research/ordinary12-qcube92-candidate/observations/halt2-attempt01/terminal.json'
A=D/'reviews/ordinary12-xq91-serialized-import-independent/observations/attempt01/result.json'
C=D/'research/ordinary12-ipra-bridge/free-j-symbolic-congruence-prototype/FreeJGraphCongruenceExplore.lean'
PAIR=D/'research/ordinary12-ipra-bridge/compact44-graph-band-pair-prototype/evidence/receipt.json'
PIN={P/'XQ91Halt.lean':'076d89c30680bc31774f2957fc06d1217dc1ac298d3815d3ca8a632e306fc5df',
 P/'HALT.md':'0d26578d48ede924ee4dab3b363c36218e082700ad18effe8cb8695b90416e9e',
 P/'run-halt.py':'bbdf6281fe2649e43d0b79e368d22ca41d5cbad7a9444b7389aec5d6ae9edb74',
 O/'terminal.json':'c803da72a3e41dd422dc697425bf20ccf1bb4624be67ac0138a0ce42e39310c5',
 O/'source.txt':'076d89c30680bc31774f2957fc06d1217dc1ac298d3815d3ca8a632e306fc5df',
 O/'runner-source.txt':'bbdf6281fe2649e43d0b79e368d22ca41d5cbad7a9444b7389aec5d6ae9edb74',
 O/'stdout':'b2f56eed9d9d53d8f17b0a234ababec60044ece4cd3bcaa1bd601eaa31f9a89b',
 BASE:'8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f',
 A:'87f7fad28524346b6921bda2f180f763417e98a0209063a7fae7fb579aea3787',
 C:'d748f8bbad7a45a328322eec1acd4643bc3e2c3f40d015b6b653f790fd8978d0',
 PAIR:'b957b92e181a90f5dd0d1b5aa2adabb12eb7ed8eac463e47c19356e2ca5182a7'}
FAILS={'halt-attempt01':('09e75d8f003487cd4aa09f279484d6a8d716e1f4eb9c7d6b8ab764e94f0c2105','5f34d4d5457635f215eda5c1ae7d20d4d95896001cafe22ef56e6a6b4af11075'),
       'halt-attempt03':('1b4d958b0ec729398741c28b257d25f2125c4980ec56a8aed77656a3cc737ac3','e8ec5144d4483ded67e42029f7e7b0dc2290da1227cb042aa587c55cb989cefe')}
def need(v,m):
 if not v:raise SystemExit(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
for p,h in PIN.items():need(sha(p)==h,'input mismatch '+str(p))
s=(P/'XQ91Halt.lean').read_text();cs=C.read_text();r=json.loads((O/'terminal.json').read_text());base=json.loads(BASE.read_text());audit=json.loads(A.read_text());pair=json.loads(PAIR.read_text())
need(s.splitlines()[:3]==['import XQ91Model','import QCube92Halt','import DiophantineConsistency.FreeJRadixAlignment'],'direct imports mismatch')
need('variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in s,'model assumptions mismatch')
for marker in ('FreeJGraphCongruenceExplore.symbolic_aligned','CompactFixedBeta.beta_identity (V:=V)',
 'CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat old','rfl rfl holdpos holdzero',
 'FreeJQCube92Model.zero_iff_transformed naturalPorts v','FreeJSumSquares.zero_iff_literal p old',
 'have old0 : old 0 = v 0','have old5 : old 5 = v 5','have hwpos : 0<w',
 'have htrans : FreeJXQ91Model.transform naturalPorts u = v',
 'internalZero_positiveShift','tsub_add_cancel_of_le','rw [byteP_eq]'):
 need(marker in s,'missing proof ingredient '+marker)
need('theorem symbolic_aligned (B K L H : ℕ) (v : Fin 12 → V)' in cs and
 '(hB : (B:V)+1=Exp.exp ((67:V)*8807)) (hL : L=lowNat) (hH : H=highNat)' in cs and
 '(hv : ∀ j,0<v j)' in cs and '(hz : InternalZero (literal (fun j => (ports B K L H j:ℤ))) v)' in cs,
 'symbolic alignment hypotheses mismatch')
halt='(∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0)'
for name,left in [('positive_model_iff','InternalZero (FreeJXQ91.graph p).output v'),
 ('shifted_model_iff','InternalZero (positiveShift (FreeJXQ91.graph p).output) x'),
 ('shifted_byte_model_iff','InternalZero (positiveShift (FreeJXQ91.graph byteP).output) x')]:
 section=s.split('theorem '+name+' :',1)[1].split(':=',1)[0];need(left in section and halt in section,'halt theorem statement mismatch '+name)
need('InternalZero (FreeJQCube92.graph p).output v' in s.split('theorem positive_zero_iff :',1)[1].split(':= by',1)[0],'92 existence side mismatch')
need(pair['status']=='PASS_PAIRED_GRAPH_BAND' and len(pair['runs'])==2,'paired alignment receipt mismatch')
for run in pair['runs']:
 steps=[x for x in run['steps'] if x['module']=='DiophantineConsistency.FreeJGraphCongruenceExplore']
 need(len(steps)==1 and steps[0]['compiler_exit']==steps[0]['deps_exit']==0 and
      steps[0]['source_sha256']==PIN[C] and steps[0]['object_sha256']=='545daf0eff0f2cc4576b456fd6f73e84a714fe3759d8cdff71874497fd20b448' and
      any(x[0]=='FreeJGraphCongruenceExplore.symbolic_aligned' for x in steps[0]['axiom_reports']),'paired symbolic-alignment step mismatch')
need(r['exit']==0 and r['reason'] is None and r['base_unchanged'] and r['extra_unchanged'] and r['union_unchanged'],'halt attempt failed')
need(r['source_sha256']==r['source_after']==sha(P/'XQ91Halt.lean') and r['runner_sha256']==r['runner_after']==sha(P/'run-halt.py'),'source or runner mismatch')
need(r['base_receipt_sha256']==sha(BASE) and r['serialized_audit_sha256']==sha(A),'base or ancestry pin mismatch')
lean=Path(r['command'][0]);need(r['lean_sha256']==r['lean_after']==sha(lean),'Lean binary drift')
need(len(r['samples'])==2 and min(x['mem_available_kib'] for x in r['samples'])==18455396 and max(len(x['lean']) for x in r['samples'])==1,'resource sample mismatch')
expected=''.join("'FreeJXQ91Halt."+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for n in ('old_X_quotient','positive_zero_iff','positive_model_iff','shifted_model_iff','shifted_byte_model_iff'))
need((O/'stdout').read_text()==expected and not (O/'stderr').read_bytes() and sha(O/'stdout')==r['stdout_sha256'] and sha(O/'stderr')==r['stderr_sha256'],'unexpected Lean output')
output=Path(r['output_root'])/'XQ91Halt.olean';need(sha(output)==r['object_sha256']=='3fe8d3122f354dbce4e2b8ded9964d0aa05c1589b0984113a95a2ba678b01799','output object mismatch')
need(sha(Path(r['output_root'])/'XQ91Halt.lean')==r['source_sha256'],'compiled source mismatch')
need(r['base_count']==len(base['union'])==1291 and r['union_count']==len(r['union'])==1294,'union counts')
extras={'XQ91.olean','XQ91Model.olean','QCube92Halt.olean'}
need(set(r['union'])==set(base['union'])|extras and all(r['union'][k]==v for k,v in base['union'].items()),'union membership/base mismatch')
need('FreeJRootBinding.olean' not in r['union'] and 'QCube92Existence.olean' not in r['union'],'excluded duplicate module present')
lib=Path(r['lean_path'].split(':')[0])
def verify_union():
 actual={p.relative_to(lib).as_posix():p for p in lib.rglob('*') if p.is_file()};need(set(actual)==set(r['union']),'live union membership drift')
 for rel,p in actual.items():
  x=r['union'][rel];need(p.is_symlink() and os.readlink(p)==x['link'] and str(p.resolve())==x['resolved'] and sha(p)==x['sha256'],'union object drift '+rel)
verify_union()
for name in ('XQ91','XQ91Model','QCube92Halt'):need(r['union'][name+'.olean']['sha256']==r['extra'][name]['object_sha256'],'extra hash mismatch '+name)
for name,items in r['declared_imports'].items():
 declared=[]
 for line in (P/name).read_text().splitlines():
  if line.startswith('import '):declared.extend(line.removeprefix('import ').split())
 need(declared==[x['module'] for x in items],'source import list mismatch '+name)
 for item in items:
  rel=item['module'].replace('.','/')+'.olean';need(rel in r['union'] and r['union'][rel]['sha256']==item['sha256'],'declared object mismatch '+rel)
need(audit['planned_imports']==['XQ91Model','QCube92Halt','DiophantineConsistency.FreeJRadixAlignment'] and len(audit['planned_project_ancestors'])==741,'serialized project plan mismatch')
congruence='DiophantineConsistency.FreeJGraphCongruenceExplore';rel=congruence.replace('.','/')+'.olean'
need(congruence in audit['planned_project_ancestors'] and audit['roots']['QCube92Halt']['selected'][congruence]['sha256']==r['union'][rel]['sha256']=='545daf0eff0f2cc4576b456fd6f73e84a714fe3759d8cdff71874497fd20b448','transitive symbolic object mismatch')
for name,(receipt_hash,log_hash) in FAILS.items():
 folder=P/'observations'/name;need(sha(folder/'terminal.json')==receipt_hash and sha(folder/'stdout')==log_hash,'failure record hash mismatch '+name)
 f=json.loads((folder/'terminal.json').read_text());need(f['exit']!=0 and f['object_sha256'] is None and 'excessive memory consumption' in (folder/'stdout').read_text(),'failed proof misreported '+name)
fail=P/'observations/halt-attempt02/DRIVER_FAILURE.md';need(sha(fail)=='f047e1e45667c2889813ed28acc0471777057028ff3c30fb4e6eb9b6651661b3' and 'exit status were not captured' in fail.read_text() and not (fail.parent/'terminal.json').exists(),'unobserved attempt02 child failure was misreported')
prior=subprocess.run([sys.executable,'-I','-S','-B',str(D/'reviews/ordinary12-xq91-serialized-import-independent/audit.py')],capture_output=True,check=True);need(not prior.stderr and json.loads(prior.stdout)['planned_project']==741,'prior serialized audit failed')
verify_union()
for p,h in PIN.items():need(sha(p)==h,'input changed during review '+str(p))
need(sha(output)==r['object_sha256'],'output changed during review')
print(json.dumps({'status':'PASS','halt_attempt_exit':r['exit'],'base_objects':len(base['union']),
 'selected_union_objects':len(r['union']),'added_objects':sorted(extras),'prior_serialized_audit':'PASS',
 'symbolic_alignment_paired_object_and_source':'PASS','failed_attempts_preserved':True,
 'attempt02_child_exit':'UNOBSERVED','halt_object_sha256':r['object_sha256']},indent=2))
