#!/usr/bin/env python3
"""Portable replay of team-authored finite and unbounded mathematical checkers.
Python standard library only. No network, installation, or downloaded-code execution.
All recorded evidence is preserved; fresh executions use a temporary working copy.
"""
import argparse,ast,concurrent.futures,hashlib,json,os,shutil,subprocess,sys,tempfile,time
from pathlib import Path
if not __debug__ or sys.flags.optimize:raise RuntimeError('Enabled assertions required; do not use -O or PYTHONOPTIMIZE')
P=Path(__file__).resolve().parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text())
def parse(p):
 d={}
 for s in p.read_text().splitlines():
  if s and not s.startswith('#'):
   q,b,w,m,r=s.split();k=int(q),int(b);assert k not in d;d[k]=(int(w),m,int(r))
 return d

def manifest():
 m=load(P/'MANIFEST.json');n=0
 for x in m['files']:
  q=P/x['path'];assert q.is_file() and q.stat().st_size==x['bytes'] and sha(q)==x['sha256'],('Manifest mismatch',x['path']);n+=1
 return n

def main():
 a=argparse.ArgumentParser();a.add_argument('--quick',action='store_true',help='Skip the four complete universal replays; retain local proof, source, boot and concrete checks');a.add_argument('--output',type=Path,default=P/'replay_result.json');args=a.parse_args()
 start=time.monotonic();n=manifest();jobs=[]
 with tempfile.TemporaryDirectory(prefix='bb242-replay-') as temp:
  W=Path(temp)/'work';shutil.copytree(P,W,ignore=shutil.ignore_patterns('__pycache__','replay_result.json'))
  def run(script,*params):
   t=time.monotonic();p=W/script
   cp=subprocess.run([sys.executable,'-B',str(p),*map(str,params)],cwd=p.parent,text=True,capture_output=True,env={**os.environ,'PYTHONOPTIMIZE':'','PYTHONDONTWRITEBYTECODE':'1'})
   if cp.returncode:raise RuntimeError(f'{script} failed:\n{cp.stdout}\n{cp.stderr}')
   return {'script':script,'returncode':cp.returncode,'seconds':round(time.monotonic()-t,3)}
  scripts=['root-proof/fold15_local_proof.py','local-proof/prove_local_folds.py','runtime/check_local_blocks_independent.py','runtime/check_boots.py','baseline243/independent-runtime/check_table_and_boot.py','baseline243/independent-runtime/check_local_compensation.py','baseline243/independent-runtime/check_source_rotation.py']
  with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:jobs.extend(ex.map(run,scripts))
  for i,name in enumerate(('fold15_27','fold27_50','fold27_171'),1):
   assert parse(W/f'runtime/survivor_{i}.tm')==parse(W/f'local-proof/candidates/{name}/machine.tm')
   assert parse(W/f'runtime/survivor_{i}_old.tm')==parse(W/f'local-proof/candidates/{name}/machine_old.tm')
   d=load(W/f'runtime/survivor_{i}_boot.json');assert d['status']=='EXACT_WHOLE_BLANK_PASS' and d['blank_transitions']==(407979,408291,407985)[i-1] and d['ones']==351
  root=load(W/'root-proof/fold15_local_proof_result.json');assert root['finite_local_implications']==root['positive_block_checks']==7696
  local=load(W/'local-proof/local_proofs.json');assert local['invariant_checks']==7640 and len(local['candidates'])==3
  assert load(W/'runtime/local_blocks_independent.json')['status']=='ALL_THREE_INDEPENDENT_LOCAL_PROOFS_PASS'
  assert load(W/'baseline243/independent-runtime/source_rotation_and_composition.json')['status']=='UNIVERSAL_SOURCE_ROTATION_AND_FRAME_COMPOSITION_PASS'
  with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:
   jobs.extend(ex.map(lambda i:run('runtime/crosscheck_instantiation.py',i),(1,2,3)))
  for i in (1,2,3):assert load(W/f'runtime/survivor_{i}_crosschecks.json')==load(P/f'runtime/survivor_{i}_crosschecks.json')
  # The same universal proof implementation validates the baseline and candidates.
  for name in ('symbolic_runtime.py','independent_runtime.py','run_symbolic_checked.py'):
   assert (W/'runtime'/name).read_bytes()==(W/'baseline243/independent-runtime'/name).read_bytes()
  universal=[]
  if not args.quick:
   tasks=[(f'runtime',f'survivor_{i}_old.tm',f'survivor_{i}_universal.json',i)for i in (1,2,3)]+[('baseline243/independent-runtime','../sources/candidate-combined243__zfc_combined243_old.tm','combined243_universal.json',0)]
   def full(t):
    directory,table,out,i=t;d=W/directory;sites=d/('sites_logical.json' if i else '../sources/candidate-combined243__sites_logical.json')
    job=run(f'{directory}/run_symbolic_checked.py','--table',d/table,'--sites',sites,'--output',d/out)
    got=load(d/out);prior=load(P/directory/out)
    assert got['status']=='UNIVERSAL_MATHEMATICAL_PASS' and got['cases']==got['expected_cases']==8390
    for k in ('table_sha256','sites_sha256','checker_sha256','helper_sha256','input_validation','symbolic_steps','minimum_actual_steps','blocks','directly_used_rows'):assert got[k]==prior[k],(i,k)
    cases=out.replace('.json','_cases.json');assert load(d/cases)==load(P/directory/cases)
    return job,{'candidate':i,'status':got['status'],'cases':got['cases'],'symbolic_steps':got['symbolic_steps'],'minimum_duration':got['minimum_actual_steps'],'cases_exact_match':True}
   with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:
    for job,result in ex.map(full,tasks):jobs.append(job);universal.append(result)
  output={'status':'QUICK_REPLAY_PASS'if args.quick else'FULL_FRESH_REPLAY_PASS','manifest_files_checked':n,'all_three_canonical_serializations_equivalent':True,'root_all_tape_checks':7696,'common_guard_checks':7640,'concrete_crosschecks_per_candidate':133,'universal_runs':universal,'jobs':jobs,'python':sys.version,'optimization':sys.flags.optimize,'seconds':round(time.monotonic()-start,3),'scope':'Fresh execution of own finite local proof, exact whole-tape bootstrap, source closure and unbounded runtime induction; not proof-assistant or independent source-theory calibration'}
  args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(output,indent=2)+'\n');print(json.dumps(output,indent=2))
if __name__=='__main__':main()
