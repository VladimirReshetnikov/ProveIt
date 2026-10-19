#!/usr/bin/env python3
"""Fresh primary241 replay plus verified frozen242 dependencies.
No network, packages, supplied repository-code execution, or writes to source evidence.
"""
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile,time,zipfile
from pathlib import Path
if not __debug__ or sys.flags.optimize:raise RuntimeError('Enabled assertions required; disable -O and PYTHONOPTIMIZE')
P=Path(__file__).resolve().parent
ZIP_SHA='c9f2d7571b5ca6beae6591b6d6db299d733834df7f861145799019fedf43e22d'
MANIFEST242_SHA='1b10257e6455d493e392416355fd7ba87a8a70b4e64c4de58b3665ed9bee2cf4'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text())
def table(path):
 out={}
 for line in path.read_text().splitlines():
  if line and not line.startswith('#'):
   q,b,w,d,z=line.split();key=int(q),int(b);assert key not in out;out[key]=(int(w),d,int(z))
 return out

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--quick',action='store_true',help='Skip fresh primary241 unbounded replay, retaining all other checks');ap.add_argument('--output',type=Path,default=P/'replay_result.json');args=ap.parse_args();start=time.monotonic();m=load(P/'MANIFEST.json')
 for row in m['files']:
  p=P/row['path'];assert p.is_file()and p.stat().st_size==row['bytes']and sha(p)==row['sha256'],('Manifest mismatch',row['path'])
 deps=P/'dependencies';z=deps/'BusyBeaver_242_Research_2026-10-18.zip';assert sha(z)==ZIP_SHA
 rec=load(deps/'BusyBeaver_242_Release_Validation.json');assert rec['status']=='FINAL_RELEASE_VALIDATED'and rec['release_files']['zip_sha256']==ZIP_SHA and rec['fresh_extraction_result']['status']=='FULL_FRESH_REPLAY_PASS'
 assert sha(deps/'FINAL_EXTRACTION_REPLAY.json')==rec['fresh_extraction_replay_sha256']
 jobs=[]
 with tempfile.TemporaryDirectory(prefix='bb241-replay-')as tmp:
  W=Path(tmp)/'companion';shutil.copytree(P,W,ignore=shutil.ignore_patterns('__pycache__','replay_result.json'));D=Path(tmp)/'inherited'
  with zipfile.ZipFile(z)as archive:
   assert archive.testzip()is None
   for info in archive.infolist():
    name=Path(info.filename);assert not name.is_absolute()and '..'not in name.parts and(info.external_attr>>16)&0o170000!=0o120000
   archive.extractall(D)
  base=D/'busybeaver242-research';assert sha(base/'MANIFEST.json')==MANIFEST242_SHA
  assert(W/'runtime/baseline242_old.tm').read_bytes()==(base/'runtime/survivor_1_old.tm').read_bytes()
  assert(W/'runtime/sites_logical.json').read_bytes()==(base/'runtime/sites_logical.json').read_bytes()
  old243=table(base/'baseline243/sources/candidate-combined243__zfc_combined243_old.tm');new241=table(W/'runtime/candidate_1_old.tm')
  direct={(15,0):(0,'L',32),(17,0):(0,'L',106),(17,1):(1,'L',37),(18,0):(0,'L',15),(46,0):(0,'R',17),(47,0):(0,'L',15),(50,0):(0,'R',17),(65,0):(0,'L',15)}
  assert set(old243)-set(new241)=={(q,b)for q in(27,39)for b in(0,1)}
  assert {k:v for k,v in new241.items()if old243[k]!=v}==direct
  spec=load(W/'DIRECT_CONSTRUCTION.json');assert spec['deleted_inherited_states']==[27,39]and spec['retained_row_edits']==[{'state':q,'read':b,'write':w,'direction':d,'target':z}for(q,b),(w,d,z)in sorted(direct.items())]

  for n in('independent_runtime.py','symbolic_runtime.py','run_symbolic_checked.py'):assert(W/'runtime'/n).read_bytes()==(base/'runtime'/n).read_bytes()
  def run(script,*params):
   t=time.monotonic();cp=subprocess.run([sys.executable,'-B',str(script),*map(str,params)],cwd=script.parent,capture_output=True,text=True,env={**os.environ,'PYTHONOPTIMIZE':'','PYTHONDONTWRITEBYTECODE':'1'})
   if cp.returncode:raise RuntimeError(f'{script.name}: {cp.stdout}\n{cp.stderr}')
   jobs.append({'script':str(script.relative_to(Path(tmp))),'returncode':cp.returncode,'seconds':round(time.monotonic()-t,3)})
  # Already validated inherited universal receipts stay explicitly inherited.
  run(base/'verify_all.py','--quick','--output',Path(tmp)/'dependency_quick.json')
  dependency=load(Path(tmp)/'dependency_quick.json');assert dependency['status']=='QUICK_REPLAY_PASS'and dependency['manifest_files_checked']==117
  run(W/'root-proof/check.py');run(W/'root-proof/boot.py');run(W/'runtime/check_local_and_boot.py');run(W/'runtime/crosscheck_instantiation.py')
  for name in('candidate_1.tm','candidate_1_old.tm','renumbering.json'):assert(W/'runtime'/name).read_bytes()==(P/'runtime'/name).read_bytes()
  root=load(W/'root-proof/result.json');assert root['invariant_implications']==root['whole_tape_block_checks']==7712
  proof=load(W/'runtime/local_proof.json');assert proof['status']=='INDEPENDENT_MAPPED_ALL_TAPE_PASS'and proof['positive_whole_tape_blocks']==7712
  boot=load(W/'runtime/boot.json');assert boot['status']=='INDEPENDENT_241_WHOLE_BLANK_PASS'and boot['blank_steps']==408419 and boot['ones']==351 and boot['clock_formula_extra_steps']==440
  assert load(W/'runtime/crosschecks.json')==load(P/'runtime/crosschecks.json')
  direct=None
  if not args.quick:
   r=W/'runtime';run(r/'run_symbolic_checked.py','--table',r/'candidate_1_old.tm','--sites',r/'sites_logical.json','--output',r/'candidate_1_universal.json')
   got=load(r/'candidate_1_universal.json');prior=load(P/'runtime/candidate_1_universal.json');assert got['status']=='UNIVERSAL_MATHEMATICAL_PASS'and got['cases']==got['expected_cases']==8390
   for k in('table_sha256','sites_sha256','checker_sha256','helper_sha256','input_validation','symbolic_steps','minimum_actual_steps','blocks','directly_used_rows'):assert got[k]==prior[k],k
   assert load(r/'candidate_1_universal_cases.json')==load(P/'runtime/candidate_1_universal_cases.json')
   direct={'status':got['status'],'cases':got['cases'],'symbolic_steps':got['symbolic_steps'],'minimum_duration':got['minimum_actual_steps'],'used_rows':len(got['directly_used_rows']),'all_case_outputs_exact_match':True}
  output={'status':'QUICK_COMPANION_REPLAY_PASS'if args.quick else'FULL_FRESH_241_COMPANION_REPLAY_PASS','manifest_files_checked':len(m['files']),'inherited_zip_sha256':ZIP_SHA,'inherited_242_243_universal_status':'Preserved full PASS receipts with exact byte bindings; not freshly rerun in this companion replay','fresh_inherited_checks':dependency,'direct_combined243_patch':'PASS: delete27/39, eight exact retained-row edits; proof composes through242','fresh_241_local_implications':7712,'fresh_241_positive_blocks':7712,'fresh_241_blank_steps':408419,'fresh_241_concrete_checks':133,'fresh_241_universal':direct,'jobs':jobs,'seconds':round(time.monotonic()-start,3),'python':sys.version,'optimization':sys.flags.optimize,'scope':'Ordinary all-tape mathematical proof and direct unbounded runtime induction; inherited calibrated source theorem, no new proof-assistant endpoint'}
  args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(output,indent=2)+'\n');print(json.dumps(output,indent=2))
if __name__=='__main__':main()
