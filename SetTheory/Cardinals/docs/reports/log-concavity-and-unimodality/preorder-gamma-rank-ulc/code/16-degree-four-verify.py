#!/usr/bin/env python3
"""Portable exact replay. No optimization solver or producer verifier is imported."""
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile,time
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):
 raise SystemExit('Exact replay requires assertions: do not use python -O/-OO or PYTHONOPTIMIZE.')
ROOT=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--mode',choices=['hashes','fast','full'],default='fast');ap.add_argument('--allow-incomplete',action='store_true');ap.add_argument('--output',type=Path,default=ROOT/'verification_results');args=ap.parse_args()
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
M=json.loads((ROOT/'MANIFEST.json').read_text())
for name,h in M['sha256'].items():
 p=ROOT/name;assert p.is_file() and digest(p)==h,('MANIFEST mismatch',name)
print('PASS manifest',len(M['sha256']),'files',flush=True)
S=ROOT/'sources';spec=json.loads((S/'preorder-gamma-degree4-independent-audit/four-attachment/approved_replay_inputs.json').read_text());expected=spec['complete_templates']
# Pin fixed kernels to the immutable independent coverage receipts, even in fast mode.
I0=S/'preorder-gamma-degree4-independent-audit';D0=S/'preorder-gamma-degree4'
assert digest(D0/'pendant10_coefficients.csv')==json.loads((I0/'certificate_audit.json').read_text())['csv_sha256']
k2=json.loads((I0/'two-attachment/kernel_audit.json').read_text())
for name,h in k2['sha256'].items():assert digest(S/Path(name).relative_to('/workspace/shared'))==h,name
for branch,key in [('three-attachment','sha256'),('four-attachment','input_sha256')]:
 data=json.loads((I0/branch/'kernel_audit.json').read_text())
 for name,h in data[key].items():assert digest(D0/branch/name)==h,(branch,name)
print('PASS independently approved kernel input pins',flush=True)
# Ordinary mathematical dependencies are checked against independently approved proof hashes.
proofs=[('preorder-gamma-degree4/EXTERIOR_LORENTZIAN_LEMMA.md','preorder-gamma-degree4/exterior_lorentzian_audit_receipt.json'),('balanced-core-gamma-research/BALANCED_LAST_GAP_PROOF.md','balanced-core-gamma-research/independent-audit/balanced_last_gap_audit_receipt.json'),('balanced-core-gamma-research/unbalanced-core/UNBALANCED_LAST_GAP_PROOF.md','balanced-core-gamma-research/unbalanced-core/independent-audit/last_gap_audit_receipt.json')]
proofs.append(('balanced-core-gamma-research/BALANCED_REAL_ROOTEDNESS_PROOF.md','balanced-core-gamma-research/independent-audit/balanced_real_rootedness_audit_receipt.json'))
proofs.extend([('balanced-core-gamma-research/incomplete-core/DISJOINT_CORE_EDGES_REAL_ROOTEDNESS.md','balanced-core-gamma-research/incomplete-core/independent-audit/disjoint_core_edges_audit_receipt.json'),('balanced-core-gamma-research/incomplete-core/TWO_BY_TWO_ROLE_COVER_THEOREM.md','balanced-core-gamma-research/incomplete-core/independent-audit/two_by_two_role_cover_audit_receipt.json')])
proofs.append(('balanced-core-gamma-research/incomplete-core/ELEMENTARY_STABILITY_OPERATORS.md','balanced-core-gamma-research/incomplete-core/independent-audit/elementary_stability_operators_audit_receipt.json'))
for proof,receipt in proofs:
 data=json.loads((S/receipt).read_text());pin=data['proof_sha256'] if 'proof_sha256' in data else data['sha256']['/workspace/shared/'+proof]
 assert digest(S/proof)==pin,proof
ordinary=json.loads((S/'preorder-gamma-degree4-independent-audit/four-attachment/ordinary_global_gap_approvals.json').read_text())
for rec in ordinary['gaps']:
 receipt=Path(rec['audit_receipt']);receipt=S/receipt.relative_to('/workspace/shared') if receipt.is_absolute() else S/'preorder-gamma-degree4-independent-audit/four-attachment'/receipt
 data=json.loads(receipt.read_text())
 if 'proof_sha256' in data:assert digest(S/Path(rec['proof']).relative_to('/workspace/shared'))==data['proof_sha256']
 else:assert rec['template']==9,('missing ordinary-proof pin',rec['template'])
for r in spec['approved_global_certificates']:
 p=S/Path(r['certificate']).relative_to('/workspace/shared');assert digest(p)==r['sha256']
assert len({(r['template'],r['gap'])for r in spec['approved_global_certificates']})==len(spec['approved_global_certificates'])
print('PASS pinned ordinary proofs and approved global inputs;',len(expected),'of76 templates complete',flush=True)
if args.mode=='hashes':print('HASH-ONLY CHECK: no algebra or exhaustive enumeration was replayed');sys.exit(0)
if len(expected)!=76 and not args.allow_incomplete:raise SystemExit('This checkpoint is incomplete. Use --allow-incomplete to replay only its explicitly approved scope.')
args.output.mkdir(parents=True,exist_ok=True);env=dict(os.environ,PYTHONINTMAXSTRDIGITS='0');steps=[];start=time.time()
with tempfile.TemporaryDirectory(prefix='degree4-replay-')as tmp:
 W=Path(tmp)/'sources';shutil.copytree(S,W)
 # Only execution copies are relocated. Original source and certificate bytes stay immutable.
 for p in W.rglob('*'):
  if p.is_file() and p.suffix in ['.py','.cpp','.inc']:
   text=p.read_text();text=text.replace('/workspace/shared',str(W));p.write_text(text)
 I=W/'preorder-gamma-degree4-independent-audit';D=W/'preorder-gamma-degree4';A=I/'four-attachment';F=D/'four-attachment';py=sys.executable
 # Historical archive transport assertion is superseded by the checked complete manifest.
 p=I/'audit_certificate.py';text=p.read_text();a=text.index("archive=BASE/");b=text.index('seen=set();',a);text=text[:a]+'archive_count=0 # transport integrity is checked by the package manifest\narchive=Path('+repr(str(ROOT/'MANIFEST.json'))+')\n'+text[b:];text=text.replace('archive_sha256=','transport_manifest_sha256=');p.write_text(text)
 # Never let a historical receipt stand in for a replay that was omitted.
 for pattern in ['global_gap*_receipt.json','medium_checkpoint*_batch_audit.json','small_faces_incremental_audit.json']:
  for p in A.glob(pattern):p.unlink()
 def run(label,argv):
  print('RUN',label,flush=True);t=time.time();log=args.output/(label+'.log')
  with log.open('w')as f:subprocess.run(list(map(str,argv)),cwd=W,env=env,stdout=f,stderr=subprocess.STDOUT,check=True)
  steps.append({'step':label,'seconds':time.time()-t,'log':log.name});print('PASS',label,round(time.time()-t,2),'seconds',flush=True)
 def compile_run(label,source,argv):
  exe=source.with_suffix('.replay');run(label+'_compile',['g++','-std=c++17','-O2',source,'-o',exe]);run(label,[exe,*argv])
 if args.mode=='full':
  hall=I/'hall_pairs_replay.csv';compile_run('a0_a1_kernel',I/'recount_hall.cpp',[hall]);assert hall.read_bytes()==(D/'pendant10_coefficients.csv').read_bytes()
  a2=I/'two-attachment';run('a2_prepare',[py,a2/'prepare_representatives.py']);compile_run('a2_kernel',a2/'recount_a2.cpp',[a2/'representatives.tsv'])
  a3=I/'three-attachment';run('a3_prepare',[py,a3/'prepare.py']);compile_run('a3_kernel',a3/'recount.cpp',[a3/'representatives.txt'])
  run('a4_prepare',[py,A/'prepare.py']);compile_run('a4_kernel',A/'recount.cpp',[A/'representatives.txt'])
 run('a1_quadratic_algebra',[py,I/'audit_certificate.py'])
 run('a2_positivity_and_faces',[py,D/'audit-positivity-independent/audit.py'])
 run('a3_positivity_and_faces',[py,I/'three-attachment/audit_positivity.py'])
 run('a4_face_coverage',[py,A/'audit_face_orbits.py'])
 groups={'whole_gap':[],'core_correction_E':[]}
 for r in spec['approved_global_certificates']:
  target=r['target'];assert target in groups,target;groups[target].append(W/Path(r['certificate']).relative_to('/workspace/shared'))
 run('a4_global_square_identities',[py,A/'audit_global_binomial_squares.py',*groups['whole_gap']]);fresh=A/'global_gap_full_replay_receipt.json';shutil.copy2(A/'global_binomial_square_audit.json',fresh)
 if groups['core_correction_E']:
  run('a4_core_correction_identities',[py,A/'audit_global_core_correction.py',*groups['core_correction_E']]);shutil.copy2(A/'global_core_correction_audit.json',A/'global_gap3_coreE_replay_receipt.json')
 run('a4_small_faces',[py,A/'audit_small_faces.py','--certificates',F/'small-faces/certificates.jsonl'])
 run('a4_medium_faces',[py,A/'audit_population_batch.py','--batch',F/'medium-faces','--name','medium_checkpoint2','--certificates',F/'medium-faces/certificates_checkpoint2.jsonl','--approved-global-receipt',fresh])
 run('a4_template9_correction',[py,A/'audit_core_correction.py'])
 run('a4_complete_coverage_union',[py,A/'refresh_progress.py']);actual=json.loads((A/'incremental_progress.json').read_text());assert actual['complete_templates']==expected,(actual['complete_templates'],expected)
 if len(expected)==76:assert actual['remaining_tasks']==0
 for p in A.glob('*replay_receipt.json'):shutil.copy2(p,args.output/p.name)
 shutil.copy2(A/'incremental_progress.json',args.output/'a4_coverage_replay.json')
result={'mode':args.mode,'complete_templates':expected,'remaining_templates':sorted(set(range(76))-set(expected)),'all_fixed_certificate_algebra_replayed':True,'kernels_independently_regenerated':args.mode=='full','ordinary_proofs':'approved source hashes checked; mathematical proof dependencies remain explicit','prior_theorems':'dependency ZIP hashes checked; their own replays are separate','seconds':time.time()-start,'steps':steps}
(args.output/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS exact replay;',len(expected),'of76 complete; mode',args.mode,flush=True)
