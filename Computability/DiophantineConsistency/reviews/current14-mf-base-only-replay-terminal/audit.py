#!/usr/bin/env python3
"""Post-exit comparison and artifact audit of both same-provider client runs."""
import hashlib,importlib.util,json
from pathlib import Path
if not __debug__:raise SystemExit('refusing optimized Python')
HERE=Path(__file__).resolve().parent;TASK=HERE.parents[1];PACKET=TASK/'research/current14-mf-base-only-endpoint-replay'
SUP=PACKET/'supervisor.py';OBS=PACKET/'terminal-observation.json';SP=Path('/tmp/current14-mf-base-only-replay-supervisor-20261104');REPLAY=Path('/tmp/current14-mf-base-only-replay-20261104');FIRST=Path('/tmp/current14-mf-base-only-attempt02-20261104');RESULT=HERE/'receipt.json'
EXPECTED='d1a61a05bd815afb109155be4985dedba39a15cece37a425e8e1fe88947169fa'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(c,m):
 if not c:raise ValueError(m)
def read(p):return json.loads(Path(p).read_text())
selfsha=sha(__file__);need(not RESULT.exists(),'refusing existing receipt');need(sha(SUP)==EXPECTED,'supervisor source mismatch')
obs=read(OBS);obshash=sha(OBS);sp=SP/'state.json';rp=REPLAY/'state.json';fp=FIRST/'state.json';s=read(sp);second=read(rp);first=read(fp)
need(obs['observed_session_exit']==0 and obs['supervisor_state_sha256']==sha(sp) and obs['runner_state_sha256']==sha(rp) and
     s['status']=='PASS' and s['child_exit']==0 and not s['wait_interruptions'] and s['supervisor_sha256']==EXPECTED and
     s['child_pid']==obs['runner_pid'] and s['replay_state_sha256']==sha(rp) and sha(SP/'runner.log')==s['log_sha256'], 'supervisor terminal evidence mismatch')
spec=importlib.util.spec_from_file_location('audited_replay_supervisor',SUP);supervisor=importlib.util.module_from_spec(spec);spec.loader.exec_module(supervisor);supervisor.pin()
runner=supervisor.load();driver,ctx,initial=runner.authenticate();need(initial==s['initial']['base']==first['initial']==second['initial'],'base/provider mismatch')
comparison=supervisor.compare(first,second);need(comparison==s['comparisons'],'supervisor comparison differs')
first_obs=read(supervisor.FIRST_PACKET/'terminal-observation.json')
for state,folder,parent_pid in ((first,FIRST,first_obs['runner_pid']),(second,REPLAY,obs['runner_pid'])):
 own={}
 for i,rec in enumerate(state['records']):
  name,declared,expected=runner.CLIENTS[i];source=folder/'src'/(name+'.lean');workspace=runner.SOURCES[i];obj=folder/'lib'/(name+'.olean')
  need(rec['module']==name and rec['exit']==0 and sha(source)==sha(workspace)==rec['source_sha256'] and
       obj.is_file() and sha(obj)==rec['object_sha256'] and rec['output_guards'][str(obj)]['sha256']==rec['object_sha256'],('source/object mismatch',name))
  driver.check_guard(rec['output_guards']);driver.check_guard(rec['direct_guards']);own[name]=rec['output_guards']
  for k in ('log','stderr','deps_stdout','deps_stderr'):need(sha(rec[k])==rec[k+'_sha256'],('log mismatch',name,k))
  reports=runner.reports(Path(rec['log']).read_text()+'\n'+Path(rec['stderr']).read_text(),expected)
  need([list(x) for x in reports]==rec['axiom_reports'],'axiom reports mismatch')
  direct=rec['direct_inputs'];driver.validate_dependencies(Path(rec['deps_stdout']).read_text().splitlines(),direct)
  need(set(declared)<=set(direct) and not set(direct)-set(declared)-{'Init'},('declared imports mismatch',name))
  for module,entry in direct.items():
   path=Path(entry['path']);g=rec['direct_guards'].get(str(path));need(isinstance(g,dict) and g['sha256']==entry['sha256'] and
       path.is_file() and str(path.resolve())==g['realpath'] and sha(path)==entry['sha256'],('direct guard mismatch',name,module))
   if module in ctx['manifest']['sources']:
    need(path==driver.BASE_DIR/'lib'/(module.replace('.','/')+'.olean') and g==ctx['base']['outputs'][module][str(path)],('base route mismatch',name,module))
   elif module in own:
    need(path==folder/'lib'/(module+'.olean') and g==own[module][str(path)],('client route mismatch',name,module))
   else:
    need(any(path==root/(module.replace('.','/')+'.olean') for root in (driver.PKG,driver.TOOL)) and
         g==ctx['base']['guarded_companions'][str(path)],('external route mismatch',name,module))
  for kind in ('deps','compile'):
   q=rec[kind+'_receipt'];need(q['exit']==0 and q['direct_child_reaped'] is True and q['session_drained'] is True and q['initial']['ppid']==parent_pid and
       q['initial']['pgrp']==q['initial']['session']==q['pid'] and rec[kind+'_samples'],('process receipt mismatch',name,kind))
 need(runner.file_inventory(folder/'lib')=={p for g in own.values() for p,v in g.items() if v is not None},'output inventory mismatch')
_,_,after=runner.authenticate();supervisor.pin()
for state,folder in ((first,FIRST),(second,REPLAY)):
 for rec in state['records']:
  need(sha(folder/'src'/(rec['module']+'.lean'))==rec['source_sha256'],'final staged source drift')
  driver.check_guard(rec['output_guards']);driver.check_guard(rec['direct_guards'])
  for k in ('log','stderr','deps_stdout','deps_stderr'):need(sha(rec[k])==rec[k+'_sha256'],('final log mismatch',rec['module'],k))
need(after==initial and sha(sp)==obs['supervisor_state_sha256'] and sha(rp)==obs['runner_state_sha256'] and
 sha(OBS)==obshash and sha(SUP)==EXPECTED and sha(SP/'runner.log')==s['log_sha256'] and sha(__file__)==selfsha,'final evidence drift')
row={'status':'PASS_SAME_SOURCE_REPLAY_ARTIFACT_AUDIT','outer_session_exit':obs['observed_session_exit'],
     'supervisor_state_sha256':sha(sp),'replay_state_sha256':sha(rp),'comparisons':comparison,'audit_sha256':selfsha,
     'scope':'Second source-identical run on the same provider plus artifact audit; not independent provider provenance or full transitive/dynamic ancestry.'}
with RESULT.open('x') as f:json.dump(row,f,indent=2,sort_keys=True);f.write('\n')
print(json.dumps(row,sort_keys=True))
