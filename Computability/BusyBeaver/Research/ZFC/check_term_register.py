#!/usr/bin/env python3
"""Reproduce the complete experimental register verifier and binary-table price.

Recover source50 offline using the maintained term frontend runner; perform all
new source/control suites, emit the full fixedF blank table, and finite prefix
QA. No Lean/Coq or incoming manifest suite is invoked. All writes are external.
"""
from pathlib import Path
from hashlib import sha256
import argparse,json,os,shutil,subprocess,sys,tempfile,time

SOURCES=('term_register.py','full_program.py','test_read_node.py','test_full.py',
         'supplementary.py','compile_full.py','measure_control.py')

def identity(p):
 data=p.read_bytes();return {'path':str(p),'bytes':len(data),'sha256':sha256(data).hexdigest()}

def main():
 if not __debug__:raise SystemExit('Keep assertions enabled; do not use -O/PYTHONOPTIMIZE.')
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--repo',type=Path);ap.add_argument('--source-root',type=Path,help='External authored sources, before publication.');ap.add_argument('--output',type=Path);ap.add_argument('--prepare-only',action='store_true');a=ap.parse_args()
 script=Path(__file__).resolve();repo=a.repo.resolve() if a.repo else next((p for p in script.parents if (p/'.git').exists()),None)
 if repo is None:ap.error('Pass --repo when outside checkout.')
 source=a.source_root.resolve() if a.source_root else script.parent/'term-register'
 for name in SOURCES:
  if not(source/name).is_file():ap.error('Missing source '+str(source/name))
 work=a.output.resolve() if a.output else Path(tempfile.mkdtemp(prefix='zfc-term-register-'))
 if work==repo or work.is_relative_to(repo) or(work.exists() and any(work.iterdir())):ap.error('Use new/empty external --output.')
 work.mkdir(parents=True,exist_ok=True);run=work/'run';run.mkdir()
 for name in SOURCES:shutil.copyfile(source/name,run/name)
 old=repo/'Computability/BusyBeaver/Research/ZFC/check_term_certificates.py'
 if not old.is_file():ap.error('Maintained source50/term recovery runner required.')
 record={'status':'RUNNING','runner':identity(script),'authored_sources':{n:identity(source/n) for n in SOURCES},'repository_HEAD':subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip(),
 'scratch':str(work),'checks':[],'Lean_built':False,'Coq_built':False,'incoming_manifest_checks':False,
 'scope':'Complete experimental primitive-register proof-search source, finite QA and actual full table cost; no compiler proof or smaller consistency machine claim.'}
 evidence=work/'verification.json'
 def save():evidence.write_text(json.dumps(record,indent=2)+'\n')
 env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1');env.pop('PYTHONOPTIMIZE',None);env.pop('PYTHONPATH',None)
 def execute(label,args):
  command=[sys.executable,'-B',*map(str,args)];log=work/(label+'.log');t=time.monotonic()
  with log.open('w') as stream:r=subprocess.run(command,cwd=run,env=env,stdout=stream,stderr=subprocess.STDOUT)
  record['checks'].append({'name':label,'command':command,'cwd':str(run),'returncode':r.returncode,'seconds':round(time.monotonic()-t,3),'log':str(log)});save();print(label,r.returncode,flush=True)
  if r.returncode:record['status']='FAIL';save();raise SystemExit('Inspect '+str(log))
 save()
 if a.prepare_only:record['status']='PREPARED';save();return
 frontend=work/'frontend'
 execute('frontend-recovery-and-controls',[old,'--repo',repo,'--output',frontend])
 oldresult=json.loads((frontend/'verification.json').read_text());assert oldresult['status']=='PASS';record['frontend_verification']=oldresult;save()
 common=['--repo',repo];newcommon=common+['--frontend',frontend/'run']
 jobs=[('ReadNode',[run/'test_read_node.py',*common,'--max-length','7','--output',work/'read-node-results.json'],'read-node-results.json'),
 ('full-control',[run/'test_full.py',*newcommon,'--max-length','7','--output',work/'full-results.json'],'full-results.json'),
 ('supplementary',[run/'supplementary.py',*newcommon,'--output',work/'supplementary-results.json'],'supplementary-results.json'),
 ('compile-full',[run/'compile_full.py',*newcommon,'--output',work/'compiled'],'compiled/compilation.json'),
 ('control-cost',[run/'measure_control.py',*newcommon,'--compiled',work/'compiled','--output',work/'control-cost.json'],'control-cost.json')]
 for label,args,resultpath in jobs:
  execute(label,args);result=json.loads((work/resultpath).read_text());assert result['status'] in ('PASS','compiled_experimental_complete_control');record[label]=result;save()
 assert all((run/n).read_bytes()==(source/n).read_bytes() for n in SOURCES)
 record['authored_sources_unchanged']=True;record['status']='PASS';record['seconds_in_checks']=sum(c['seconds'] for c in record['checks']);save();print('Evidence',evidence,flush=True)

if __name__=='__main__':main()
