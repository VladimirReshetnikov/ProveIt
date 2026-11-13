#!/usr/bin/env python3
"""Read-only independent check of the 92-variable halt-model author result."""
from hashlib import sha256
import json
from pathlib import Path
import os
import subprocess
import sys

D=Path(__file__).resolve().parents[2]
P=D/'research/ordinary12-qcube92-candidate'
O=P/'observations/halt2-attempt01'
BASE=D/'research/ordinary12-sum-squares-model-bridge/observations/attempt01/terminal.json'
A1=D/'reviews/ordinary12-qcube92-serialized-import-independent/observations/attempt01/result.json'
A2=D/'reviews/ordinary12-qcube92-module-collision-independent/observations/attempt01/result.json'
PIN={
 P/'QCube92Halt.lean':'4761687cb642710db6e6b10b205611b0f3920c2b0916ce13265c773ae3fa7429',
 P/'HALT.md':'a3a3acad6ce450951c91d8f119cd241d574db7dc4d673ee4769d7548db5fa77d',
 P/'run-halt2.py':'0723a9bcb8bcf8a7b5d215d8f57a7442aa2cce0e98126c8c1a5cc99b64737ac3',
 O/'terminal.json':'8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f',
 O/'source.txt':'4761687cb642710db6e6b10b205611b0f3920c2b0916ce13265c773ae3fa7429',
 O/'runner-source.txt':'0723a9bcb8bcf8a7b5d215d8f57a7442aa2cce0e98126c8c1a5cc99b64737ac3',
 O/'stdout':'77dcbb9c3ee6544c3e507e1017dc9ef91e45997ebb59b8ae0950e8aa78444c58',
 BASE:'febe3f4317dd62fa24d0194844490350f08db1176705a6ebf6db08119efba580',
 A1:'af847f4a3903770fd50bf7b7f09d597f748fa83ab0c3f4c0b7ae79dff192a615',
 A2:'d3f68298e20708297524c0e0e540091e184d451972fdb801ab9081c227779934',
 P/'observations/halt-attempt01/terminal.json':'4e04eaa339d336845538c3ebe30fecc1ff233c2b9bd54ad1fd7e2c1080534764',
 P/'observations/halt-attempt01/stdout':'fd01406bde2292141145559de00a9f56aa24c33bdd7aae6eb22bf26e1bd65498',
}
FAILS={
 'halt-preflight01':('595c7b0ab8945776e3de37ad75485bb8367ba3a25b2007c794bcfa7da1f82b74','6ec458dd97344d5d04c75e39ce2a9842d113ebdeb585a46cc9339cc3c115f987','provider overlap mismatch FreeJOrdinaryTailWitness.olean'),
 'halt-preflight02':('16a1e91c6d141654824c4893c07f5abb0312af83be95a872c2d45be677805287','17319e0d7538263071f6ec7b2454b379034e3d2e576363b8f1ae4399db1ae9c7','provider object missing in candidate union FreeJSignedTransport.olean'),
 'halt-preflight03':('3cf8c0a5de75acffd4732a35910bd148976446e2240f8818d5e5d82ce884cc46','27d7f09b94613c92bc2122736973883208824e603fb81dcdc4c40043b9bb9b32',"KeyError: '92_companions'"),
}

def need(v,m):
 if not v:raise SystemExit(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
for p,h in PIN.items():need(sha(p)==h,'input mismatch: '+str(p))
r=json.loads((O/'terminal.json').read_text());base=json.loads(BASE.read_text());a1=json.loads(A1.read_text());a2=json.loads(A2.read_text());src=(P/'QCube92Halt.lean').read_text()
need(src.splitlines()[:3]==['import QCube92NamespacedExistence','import CompactSymbolicModelUnconditionalIff','import CompactBytePortsModelIff'],'direct imports mismatch')
need('variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in src,'model assumptions mismatch')
need('ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat' in src,'fixed tuple mismatch')
need('have h := CompactFixedBeta.bounds (1 : V) (by simp)' in src,'beta proof missing')
halt='(∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0)'
for name,left in [('positive_model_iff','InternalZero (graph p).output v'),
                  ('shifted_model_iff','InternalZero (positiveShift (graph p).output) x'),
                  ('shifted_byte_model_iff','InternalZero (positiveShift (graph byteP).output) x')]:
 section=src.split('theorem '+name+' :',1)[1].split(':= by',1)[0]
 need(left in section and halt in section,'halt statement mismatch: '+name)
for marker in ('positive_zero_iff (V:=V) naturalPorts (beta_pos (V:=V))',
               'CompactSymbolicModelUnconditionalIff.model_iff (V:=V)',
               'internalZero_positiveShift', 'tsub_add_cancel_of_le', 'rw [byteP_eq]'):
 need(marker in src,'missing inspected proof ingredient: '+marker)
need(r['exit']==0 and r['reason'] is None and r['base_unchanged'] and r['extra_unchanged'] and r['union_unchanged'],'halt receipt failed')
need(r['source_sha256']==r['source_after']==sha(P/'QCube92Halt.lean') and r['runner_sha256']==r['runner_after']==sha(P/'run-halt2.py'),'source or runner drift')
lean=Path(r['command'][0]);need(r['lean_sha256']==r['lean_after']==sha(lean),'Lean binary drift')
need(r['base_receipt_sha256']==r['base_receipt_after']==sha(BASE),'base receipt drift')
need(r['ancestry_audit_sha256']==sha(A1) and r['namespaced_ancestry_audit_sha256']==sha(A2),'ancestor audit pin mismatch')
need(len(r['samples'])==3 and min(s['mem_available_kib'] for s in r['samples'])==18524376 and all(len(s['lean'])<=1 for s in r['samples']),'resource sample mismatch')
expected=''.join("'FreeJQCube92Halt."+name+"' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for name in ('beta_pos','positive_model_iff','shifted_model_iff','shifted_byte_model_iff'))
need((O/'stdout').read_text()==expected and not (O/'stderr').read_bytes() and sha(O/'stdout')==r['stdout_sha256'] and sha(O/'stderr')==r['stderr_sha256'],'unexpected axiom report')
output=Path(r['output_root'])/'QCube92Halt.olean'
need(output.is_file() and sha(output)==r['object_sha256']=='37378b4a3e6842f02c5991a69634c85f696123520dd6ca3171e2f16a2fff2a08','compiled object mismatch')
need(sha(Path(r['output_root'])/'QCube92Halt.lean')==r['source_sha256'],'compiled source mismatch')

# Independently inspect all 1,291 recorded union entries, including symlink targets.
need(r['base_count']==len(base['union'])==1288 and r['union_count']==len(r['union'])==1291,'union count mismatch')
extras={'QCube92.olean','QCube92Model.olean','QCube92NamespacedExistence.olean'}
need(set(r['union'])==set(base['union'])|extras,'union membership mismatch')
need(all(r['union'][k]==v for k,v in base['union'].items()),'94 base object selection changed')
need('FreeJRootBinding.olean' not in r['union'] and 'QCube92Existence.olean' not in r['union'],'excluded modules in union')
lib=Path(r['lean_path'].split(':')[0])
def verify_union():
 actual={p.relative_to(lib).as_posix():p for p in lib.rglob('*') if p.is_file()}
 need(set(actual)==set(r['union']),'live union membership changed')
 for rel,path in actual.items():
  recorded=r['union'][rel]
  need(path.is_symlink() and os.readlink(path)==recorded['link'] and str(path.resolve())==recorded['resolved'] and sha(path)==recorded['sha256'],'union object mismatch: '+rel)
verify_union()
for name in ('QCube92','QCube92Model','QCube92NamespacedExistence'):
 need(r['union'][name+'.olean']['sha256']==r['extra'][name]['object_sha256'],'added object hash mismatch: '+name)
# Check actual imported sources and recorded direct-object hashes, without trusting just the list.
for name,records in r['declared_imports'].items():
 source=(P/name).read_text();names=[]
 for line in source.splitlines():
  if line.startswith('import '):names.extend(line.removeprefix('import ').split())
 need(names==[x['module'] for x in records],'declared source imports mismatch: '+name)
 for record in records:
  rel=record['module'].replace('.','/')+'.olean'
  need(rel in r['union'] and r['union'][rel]['sha256']==record['sha256'],'declared import hash mismatch: '+rel)
need(all(not row['tail_in_project_ancestry'] for row in a1['roots'].values()),'tail unexpectedly in previous roots')
need(all(not row['top_level_binding_ancestor'] and row['namespaced_binding_ancestor'] and 'QCube92Existence' not in row['project_ancestors'] for row in a2['roots'].values()),'binding/old existence ancestry mismatch')
# Reinspect historical errors; they are not accepted proofs.
for name,(runner,stderr,needle) in FAILS.items():
 folder=P/'observations'/name
 need((folder/'exit-code').read_text().strip()=='1' and not (folder/'stdout').read_bytes(),'preflight did not fail as recorded: '+name)
 need(sha(folder/'runner-source.txt')==runner and sha(folder/'stderr')==stderr and needle in (folder/'stderr').read_text(),'preflight evidence mismatch: '+name)
failed=json.loads((P/'observations/halt-attempt01/terminal.json').read_text())
need(failed['exit']!=0 and 'environment already contains' in (P/'observations/halt-attempt01/stdout').read_text(),'prior duplicate-module failure mismatch')
for script in (D/'reviews/ordinary12-qcube92-serialized-import-independent/audit.py',D/'reviews/ordinary12-qcube92-module-collision-independent/audit.py'):
 check=subprocess.run([sys.executable,'-I','-S','-B',str(script)],capture_output=True,check=True)
 need(not check.stderr,'prior ancestry review stderr')
verify_union()
for p,h in PIN.items():need(sha(p)==h,'input changed during review: '+str(p))
need(sha(output)==r['object_sha256'],'halt object changed during review')
print(json.dumps({'halt_attempt_exit':r['exit'],'graph_variables':12,'base_objects':len(base['union']),
                  'selected_union_objects':len(r['union']),'added_objects':sorted(extras),
                  'prior_ancestry_reviews':'PASS','historical_failures':'PRESERVED',
                  'halt_object_sha256':r['object_sha256']},indent=2))
