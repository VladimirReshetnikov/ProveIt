#!/usr/bin/env python3
"""Observe an isolated replay and compare it with the captured first client run."""
import argparse,hashlib,importlib.util,json,os,shutil,subprocess,sys,time
from pathlib import Path
if not __debug__:raise SystemExit('refusing optimized Python')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];TASK=HERE.parents[1]
RUNNER=HERE/'runner.py';OUT=Path('/tmp/current14-mf-base-only-replay-supervisor-20261104')
FIRST=Path('/tmp/current14-mf-base-only-attempt02-20261104')
FIRST_PACKET=TASK/'research/current14-mf-base-only-endpoint-attempt02'
FIRST_AUDIT=TASK/'reviews/current14-mf-base-only-attempt02-terminal/receipt.json'
FIRST_AUDIT_EXEC=FIRST_AUDIT.parent/'audit-execution.json'
FIRST_AUDIT_SCRIPT=FIRST_AUDIT.parent/'audit.py'
PINS={RUNNER:'988112f6ab8585dfa7eff62ce22d615d7faefa593eea1978b7d071ee638ed0ed',
      HERE/'Current14LiteralPortsMF.lean':'3de8c3649e358607b85a8317a052b5ac2c0e34c24608ae5f89d1a918a7821540',
      HERE/'StructuredEndpointMF.lean':'906861b83a51dd58b043da16a0d6628925128bfc1197568eb7ba09f472622a08',
      FIRST/'state.json':'464b231aaa0e6348e626e8e5fca2e84f283adc36e56b8daac5360124efe5dc98',
      FIRST_PACKET/'terminal-observation.json':'19abaa54ff1e17122acd7c3d2ab969cce6ebab50f47b935a94cbc70b526b8bba',
      FIRST_PACKET/'Current14LiteralPortsMF.lean':'3de8c3649e358607b85a8317a052b5ac2c0e34c24608ae5f89d1a918a7821540',
      FIRST_PACKET/'StructuredEndpointMF.lean':'906861b83a51dd58b043da16a0d6628925128bfc1197568eb7ba09f472622a08',
      FIRST_AUDIT:'36e6bc9d18bc1ff609b4996e54d8aae1b6b182d55c0d36b71c3492642ea6004f',
      FIRST_AUDIT_EXEC:'7bd681a72fc4e648e36eb2d87842f6c0358a4392afe79937b9ed287820cbf0e8',
      FIRST_AUDIT_SCRIPT:'bcc40391b9d53522542d16f9e7d8c7b0a90008d237d8eefa54221b25788453ee'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(c,m):
 if not c:raise ValueError(m)
def read(p):return json.loads(Path(p).read_text())
def pin():
 for p,h in PINS.items():need(p.is_file() and sha(p)==h,('replay pin mismatch',str(p)))
def load():
 spec=importlib.util.spec_from_file_location('same_source_replay_runner',RUNNER);r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r);return r
def compare(first,second):
 need(first.get('status')=='PASS' and second.get('status')=='PASS','run state not PASS')
 a=first.get('records',[]);b=second.get('records',[])
 need(len(a)==len(b)==2,'wrong row count')
 comparisons=[]
 for x,y in zip(a,b):
  need(x['module']==y['module'] and x['exit']==y['exit']==0 and x['source_sha256']==y['source_sha256'],('row/source mismatch',x.get('module')))
  need(x['axiom_reports']==y['axiom_reports'],('axiom report mismatch',x['module']))
  need(x['object_sha256']==y['object_sha256'],('object digest mismatch',x['module'],x['object_sha256'],y['object_sha256']))
  dx={k:v['sha256'] for k,v in x['direct_inputs'].items()};dy={k:v['sha256'] for k,v in y['direct_inputs'].items()}
  need(dx==dy,('direct dependency digest mismatch',x['module']))
  comparisons.append({'module':x['module'],'source_sha256':x['source_sha256'],'object_sha256':x['object_sha256'],
                      'direct_inputs':dx,'axiom_reports':x['axiom_reports']})
 return comparisons
def check_first_evidence(obs,audit,audit_exec,first,state_sha,audit_sha):
 need(obs.get('observed_session_exit')==0 and obs.get('state_sha256')==state_sha and
      obs.get('runner_sha256')=='fae89cf5ae51f4ae5b9fe87129be41b38d19b456398cb954af14951fd0f1f7a1' and
      first.get('runner_sha256')==obs.get('runner_sha256') and first.get('status')=='PASS' and
      audit.get('status')=='PASS_RECORDED_CLIENT_ROWS_ARTIFACT_AUDIT' and audit.get('state_sha256')==state_sha and
      audit.get('audited_rows')==['Current14LiteralPortsMF','StructuredEndpointMF'] and audit.get('audit_sha256')==audit_sha and
      audit_exec.get('exit')==0 and audit_exec.get('audit_sha256')==audit_sha and json.loads(audit_exec['stdout'])==audit,
      'first run not authenticated PASS')
def gate():
 pin();r=load();need(not OUT.exists() and not r.OUT.exists(),'replay output already exists')
 obs=read(FIRST_PACKET/'terminal-observation.json');audit=read(FIRST_AUDIT);audit_exec=read(FIRST_AUDIT_EXEC);firstpath=FIRST/'state.json';first=read(firstpath)
 check_first_evidence(obs,audit,audit_exec,first,sha(firstpath),sha(FIRST_AUDIT_SCRIPT))
 driver,ctx,initial=r.authenticate();need(initial==first['initial'],'first and replay base differ')
 need(len(first['records'])==2,'first row count')
 for i,rec in enumerate(first['records']):
  name,_,expected=r.CLIENTS[i];source=FIRST/'src'/(name+'.lean');obj=FIRST/'lib'/(name+'.olean')
  need(rec['module']==name and rec['exit']==0 and sha(source)==PINS[HERE/(name+'.lean')]==rec['source_sha256'] and
       sha(obj)==rec['object_sha256'],'first source/object mismatch')
  for key in ('log','stderr','deps_stdout','deps_stderr'):need(sha(rec[key])==rec[key+'_sha256'],('first log mismatch',name,key))
  text=Path(rec['log']).read_text()+'\n'+Path(rec['stderr']).read_text();need([list(x) for x in r.reports(text,expected)]==rec['axiom_reports'],'first axiom mismatch')
  driver.check_guard(rec['direct_guards']);driver.check_guard(rec['output_guards'])
 need(r.idle_lean(),'Lean slot busy');pin()
 return r,first,{'base':initial,'first_state_sha256':sha(firstpath),'first_audit_sha256':sha(FIRST_AUDIT),
                  'first_observation_sha256':sha(FIRST_PACKET/'terminal-observation.json'),'first_audit_execution_sha256':sha(FIRST_AUDIT_EXEC)}
def wait_owned(proc):
 errors=[]
 while True:
  try:return proc.wait(),errors
  except BaseException as exc:
   errors.append(repr(exc))
   try:time.sleep(1)
   except BaseException as e:errors.append(repr(e))
def run(r,first,initial):
 need(not OUT.exists() and not r.OUT.exists() and r.idle_lean(),'output exists or Lean slot busy')
 scriptsha=sha(__file__);OUT.mkdir();log=OUT/'runner.log';statepath=OUT/'state.json';cmd=[sys.executable,'-I','-S','-B','-u',str(RUNNER),'--run']
 state={'status':'RUNNING','initial':initial,'supervisor_sha256':scriptsha,'runner_sha256':PINS[RUNNER],'command':cmd,'samples':[],
        'scope':'Same-source replay on the same provider; dynamic/transitive/between-sample ancestry inherited.'}
 def save():
  tmp=OUT/'state.tmp';tmp.write_text(json.dumps(state,indent=2,sort_keys=True)+'\n');tmp.replace(statepath)
 save();proc=None;failure=None;interruptions=[];code=None
 with log.open('xb') as stream:
  try:
   proc=subprocess.Popen(cmd,cwd=ROOT,stdout=stream,stderr=subprocess.STDOUT,start_new_session=True)
   state['child_pid']=proc.pid;save()
   while proc.poll() is None:
    sample={'memavailable_bytes':r.available(),'free_bytes':shutil.disk_usage('/tmp').free}
    try:
     inner=read(r.OUT/'state.json');sample.update({k:inner.get(k) for k in ('status','phase')});sample['rows']=len(inner.get('records',[]))
    except (FileNotFoundError,json.JSONDecodeError):pass
    state['samples'].append(sample);save();time.sleep(5)
   code=proc.wait()
  except BaseException as exc:
   failure=repr(exc)
   if proc is not None:code,interruptions=wait_owned(proc)
 state.update(child_exit=code,wait_interruptions=interruptions,log_sha256=sha(log),failure=failure)
 try:
  need(failure is None and not interruptions and code==0,('replay process failed',code,failure))
  secondpath=r.OUT/'state.json';second=read(secondpath);secondsha=sha(secondpath)
  need(second['runner_sha256']==PINS[RUNNER] and second['initial']==initial['base'],'replay terminal pins mismatch')
  comparisons=compare(first,second)
  driver,_,after=r.authenticate();need(after==initial['base'],'base changed during replay')
  for prior,folder in ((first,FIRST),(second,r.OUT)):
   for rec in prior['records']:
    name=rec['module'];need(sha(folder/'src'/(name+'.lean'))==rec['source_sha256'] and
         sha(folder/'lib'/(name+'.olean'))==rec['object_sha256'],('source/object drift after replay',name))
    for field in ('log','stderr','deps_stdout','deps_stderr'):
     need(sha(rec[field])==rec[field+'_sha256'],('log drift after replay',name,field))
    driver.check_guard(rec['direct_guards']);driver.check_guard(rec['output_guards'])
  need(sha(FIRST/'state.json')==initial['first_state_sha256'] and sha(FIRST_AUDIT)==initial['first_audit_sha256'] and
       sha(FIRST_PACKET/'terminal-observation.json')==initial['first_observation_sha256'] and
       sha(FIRST_AUDIT_EXEC)==initial['first_audit_execution_sha256'] and sha(secondpath)==secondsha and sha(__file__)==scriptsha,
       'terminal evidence drift')
  pin();state.update(status='PASS',replay_state_sha256=secondsha,comparisons=comparisons);save();print('PASS same-source replay with matching object and axiom reports',flush=True)
 except BaseException as exc:
  state.update(status='FAILED',failure=repr(exc));save();raise

def main():
 p=argparse.ArgumentParser();group=p.add_mutually_exclusive_group();group.add_argument('--run',action='store_true');group.add_argument('--check',action='store_true');args=p.parse_args();r,first,initial=gate()
 print(json.dumps({'status':'PREFLIGHT_PASS','initial':initial},sort_keys=True),flush=True)
 if args.run:run(r,first,initial)
if __name__=='__main__':
 try:main()
 except Exception as exc:print('REFUSED_OR_FAILED',repr(exc),file=sys.stderr);raise SystemExit(1)
