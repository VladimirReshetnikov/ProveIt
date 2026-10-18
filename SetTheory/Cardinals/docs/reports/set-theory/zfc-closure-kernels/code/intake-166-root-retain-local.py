from pathlib import Path
import os,sys,shutil,subprocess,time,signal,json,hashlib
root=Path(__file__).resolve().parent
origin=Path('/tmp/zfc244-248bc05936-inspection/zfc244-compensated-routing-20261018')
out=root/'retained-local';out.mkdir(exist_ok=False);pkg=out/'package';shutil.copytree(origin,pkg)
env=os.environ.copy();env.pop('PYTHONOPTIMIZE',None);env.pop('PYTHONPATH',None);env['PYTHONDONTWRITEBYTECODE']='1'
commands=[('rebuild',['rebuild_candidates.py']),('direct',['prove_contextual_fold.py']),('independent',['verify_local_stuttering.py','reference/zfc245_old.tm','candidate_1_244_old.tm','--output','retained-independent.json']),('boot',['check_new_boot.py','candidate_1_244_old.tm','retained-boot.json'])]
records=[]
for name,args in commands:
 command=[sys.executable,'-B',*args];began=time.monotonic()
 with (out/(name+'-stdout.log')).open('wb') as stdout,(out/(name+'-stderr.log')).open('wb') as stderr:
  proc=subprocess.Popen(command,cwd=pkg/'runtime',env=env,stdout=stdout,stderr=stderr,start_new_session=True)
  try:code=proc.wait(timeout=120);timedout=False
  except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);code=proc.wait();timedout=True
 record={'name':name,'command':command,'returncode':code,'timed_out':timedout,'seconds':time.monotonic()-began,'stdout':str(out/(name+'-stdout.log')),'stderr':str(out/(name+'-stderr.log'))};records.append(record)
 assert code==0 and not timedout
pairs=[('contextual_fold_proof.json','contextual_fold_proof.json'),('retained-independent.json','local-stuttering-audit.json'),('retained-boot.json','candidate_1_boot.json')]
for a,b in pairs: assert (pkg/'runtime'/a).read_bytes()==(origin/'runtime'/b).read_bytes()
for i in [1,2,3]:
 for suffix in ['244.tm','244_old.tm','renumbering.json']:
  name=f'candidate_{i}_{suffix}';assert (pkg/'runtime'/name).read_bytes()==(origin/'runtime'/name).read_bytes()
result={'status':'PASS_RETAINED_LOCAL_EVIDENCE','purpose':'Separate permanent retention of detailed local/boot outputs and child streams that the portable driver removes with its TemporaryDirectory. Not another independent checker.','records':records,'outputs_equal_delivered_records':pairs,'all_three_reconstructed_variants_equal':True,'source_files_unchanged':True,'supplied_compiler_calls':0,'manifest_audit_performed':False}
(out/'execution.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
