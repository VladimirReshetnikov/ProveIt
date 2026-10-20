from pathlib import Path
import json,os,shutil,subprocess,sys,time
import argparse,runpy
ap=argparse.ArgumentParser(description='Replay seven selected K219 checks on a fresh scratch copy')
ap.add_argument('--packets',type=Path,required=True)
ap.add_argument('--output',type=Path,required=True)
a=ap.parse_args();out=a.output.resolve()
repo=Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],text=True).strip())
if out==repo or repo in out.parents:ap.error('Output must be outside the repository')
out.mkdir(parents=True,exist_ok=False)
packet=out/'work/K219_Construction_2026-10-20'
shutil.copytree(a.packets.resolve()/'K219_Construction_2026-10-20',packet)
extract=runpy.run_path(str(Path(__file__).with_name('recover-intake186.py')))['extract']
extract((packet/'portable/vendor/K220_Construction_2026-10-20.zip').read_bytes(),out/'work/parents')
parent220=out/'work/parents/K220_Construction_2026-10-20'
extract((parent220/'portable/vendor/K221_Construction_2026-10-20.zip').read_bytes(),out/'work/parents')
parent221=out/'work/parents/K221_Construction_2026-10-20'
jobs=[]
def run(name,script,args,timeout=120):
 command=[sys.executable,'-B',str(packet/'portable'/script),*map(str,args)]
 log=out/(name+'.log');started=time.monotonic();print(name,flush=True)
 with log.open('w') as f:
  try:
   result=subprocess.run(command,cwd=packet,stdout=f,stderr=subprocess.STDOUT,timeout=timeout,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')); code,timed_out=result.returncode,False
  except subprocess.TimeoutExpired:code,timed_out=None,True
 jobs.append(dict(name=name,command=command,cwd=str(packet),log=str(log),exit_code=code,timed_out=timed_out,seconds=time.monotonic()-started))
 (out/'actual.json').write_text(json.dumps(dict(jobs=jobs,scope='Selected K219 machine checks and finite algebra. No manifest validation or recursive ancestor replay; macro equivalence and HC proof are reviewed written mathematics.'),indent=2)+'\n')
 assert code==0 and not timed_out,jobs[-1]
 print(name,'PASS',round(jobs[-1]['seconds'],2),flush=True)
run('source','build_source219.py',['--sites220',parent220/'machine/sites220.json','--out',out/'source'])
run('construction','build219.py',['--baseline',parent220,'--sites',out/'source/sites.json','--output',out/'construction'])
run('canonical-startup','canonicalize219.py',['--table',out/'construction/candidate.tm','--sites',out/'construction/sites.json','--output',out/'canonical'])
run('full-runtime','check_runtime219.py',['--baseline',parent221,'--table',out/'construction/candidate.tm','--sites',out/'construction/sites.json','--output',out/'runtime'],1200)
run('independent-audit','audit_runtime219.py',['--baseline',parent221,'--table',out/'construction/candidate.tm','--sites',out/'construction/sites.json','--runtime',out/'runtime','--driver',packet/'portable/check_runtime219.py','--canonical',out/'canonical/canonicalization.json','--output',out/'runtime_audit.json'])
for a,b in [('construction/candidate.tm','k219.native.tm'),('construction/sites.json','sites219.json'),('canonical/k219.tm','k219.tm')]: assert (out/a).read_bytes()==(packet/'machine'/b).read_bytes()
run('independent-decoder-startup','../research/encoding/audit_final219.py',[out/'construction/candidate.tm',out/'construction/sites.json',out/'literal-audit.json'])
run('finite-algebra','../research/theory/restricted_rho8_strong_countermodel.py',[])
shutil.copyfile(packet/'research/theory/generated/restricted_rho8_strong_countermodel.json',out/'finite-algebra.json')
print('ALL_SEVEN_SELECTED_K219_JOBS_PASS',flush=True)
