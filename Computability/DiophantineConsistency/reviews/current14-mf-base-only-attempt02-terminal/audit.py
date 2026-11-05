#!/usr/bin/env python3
"""One- or two-row artifact audit after an observed terminal client session."""
import hashlib,importlib.util,json,os
from pathlib import Path
if not __debug__:raise SystemExit('refusing optimized Python')
HERE=Path(__file__).resolve().parent;TASK=HERE.parents[1];PACKET=TASK/'research/current14-mf-base-only-endpoint-attempt02'
RUNNER=PACKET/'runner.py';OBS=PACKET/'terminal-observation.json';OUT=Path('/tmp/current14-mf-base-only-attempt02-20261104')
RESULT=HERE/'receipt.json';EXPECTED='fae89cf5ae51f4ae5b9fe87129be41b38d19b456398cb954af14951fd0f1f7a1'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(c,m):
 if not c:raise ValueError(m)
def read(p):return json.loads(Path(p).read_text())
startsha=sha(__file__);need(not RESULT.exists(),'refusing existing receipt')
need(OBS.is_file() and (OUT/'state.json').is_file(),'terminal observation or state missing')
obs=read(OBS);obshash=sha(OBS);statepath=OUT/'state.json';statehash=sha(statepath);state=read(statepath)
need(obs.get('state_sha256')==statehash and obs.get('observed_session_exit') in (0,1),'terminal observation mismatch')
need((state['status']=='PASS' and obs['observed_session_exit']==0 and len(state['records'])==2) or
     (state['status']=='FAILED' and obs['observed_session_exit']==1 and len(state['records']) in (1,2)),
     'no auditable terminal rows')
need(sha(RUNNER)==EXPECTED and state['runner_sha256']==EXPECTED,'runner hash mismatch')
spec=importlib.util.spec_from_file_location('mf_base_only_audit_runner',RUNNER);runner=importlib.util.module_from_spec(spec);spec.loader.exec_module(runner)
driver,ctx,initial=runner.authenticate();need(initial==state['initial'],'base authentication mismatch')
records=state['records'];outputs={};reports=[]
for i,rec in enumerate(records):
 name,declared,expected=runner.CLIENTS[i];src=OUT/'src'/(name+'.lean');workspace=runner.SOURCES[i];obj=OUT/'lib'/(name+'.olean')
 need(rec['module']==name and rec['exit']==0 and sha(src)==sha(workspace)==runner.PINS[workspace]==rec['source_sha256'],('source or row mismatch',name))
 need(obj.is_file() and not obj.is_symlink() and sha(obj)==rec['object_sha256'] and rec['output_guards'][str(obj)]['sha256']==rec['object_sha256'],('object mismatch',name))
 driver.check_guard(rec['output_guards']);outputs[name]=rec['output_guards']
 for key in ('log','stderr','deps_stdout','deps_stderr'):
  p=Path(rec[key]);need(p.is_file() and sha(p)==rec[key+'_sha256'],('log mismatch',name,key))
 need(not Path(rec['deps_stderr']).read_text(),'deps stderr not empty')
 rep=runner.reports(Path(rec['log']).read_text()+'\n'+Path(rec['stderr']).read_text(),expected)
 need([list(x) for x in rep]==rec['axiom_reports'],('axiom reports mismatch',name));reports.extend(rep)
 direct=rec['direct_inputs'];driver.validate_dependencies(Path(rec['deps_stdout']).read_text().splitlines(),direct)
 need(set(declared)<=set(direct) and not set(direct)-set(declared)-{'Init'},('declared/direct mismatch',name))
 driver.check_guard(rec['direct_guards'])
 for module,entry in direct.items():
  path=Path(entry['path']);g=rec['direct_guards'].get(str(path));need(isinstance(g,dict) and g['sha256']==entry['sha256'] and
      path.is_file() and str(path.resolve())==g['realpath'] and sha(path)==entry['sha256'],('direct guard mismatch',name,module))
  if module in ctx['manifest']['sources']:
   need(path==driver.BASE_DIR/'lib'/(module.replace('.','/')+'.olean') and
        g==ctx['base']['outputs'][module][str(path)],('base route mismatch',name,module))
  elif module in outputs:
   need(path==OUT/'lib'/(module+'.olean') and g==outputs[module][str(path)],('client route mismatch',name,module))
  else:
   roots=(driver.PKG,driver.TOOL);need(any(path==root/(module.replace('.','/')+'.olean') for root in roots) and
        g==ctx['base']['guarded_companions'][str(path)],('external route mismatch',name,module))
 for kind in ('deps','compile'):
  q=rec[kind+'_receipt'];sample=rec[kind+'_samples'];need(q['exit']==0 and q['direct_child_reaped'] is True and q['session_drained'] is True and
   q['initial']['ppid']==obs['runner_pid'] and q['initial']['pgrp']==q['initial']['session']==q['pid'] and sample,('owned process receipt mismatch',name,kind))
_,_,after=runner.authenticate();need(after==initial and sha(statepath)==statehash and sha(OBS)==obshash and sha(__file__)==startsha and sha(RUNNER)==EXPECTED,'final input drift')
row={'status':'PASS_RECORDED_CLIENT_ROWS_ARTIFACT_AUDIT','audited_rows':[r['module'] for r in records],
     'client_session_exit':obs['observed_session_exit'],'client_terminal_status':state['status'],'axiom_reports':reports,
     'state_sha256':statehash,'audit_sha256':startsha,
     'scope':'Recorded rows from one actual client session; no Lean replay, no unrecorded rows, and no full transitive/dynamic ancestry claim.'}
with RESULT.open('x') as f:json.dump(row,f,indent=2,sort_keys=True);f.write('\n')
print(json.dumps(row,sort_keys=True))
