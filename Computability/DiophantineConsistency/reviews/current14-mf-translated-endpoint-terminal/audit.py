#!/usr/bin/env python3
"""Artifact audit for one actually completed translated endpoint client."""
import hashlib,importlib.util,json
from pathlib import Path
if not __debug__:raise SystemExit('refusing optimized Python')
HERE=Path(__file__).resolve().parent;TASK=HERE.parents[1];PACKET=TASK/'research/current14-mf-translated-endpoint'
RUNNER=PACKET/'runner.py';OBS=PACKET/'terminal-observation.json';OUT=Path('/tmp/current14-mf-translated-endpoint-attempt01-20261104')
RESULT=HERE/'receipt.json';EXPECTED='8ce9ef6199d5dc9b4d51f2666fac75b8a934692f261bfede177b64668b1aee9a'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(c,m):
 if not c:raise ValueError(m)
def read(p):return json.loads(Path(p).read_text())
auditsha=sha(__file__);need(not RESULT.exists(),'refusing existing receipt')
obs=read(OBS);obshash=sha(OBS);statepath=OUT/'state.json';statehash=sha(statepath);state=read(statepath)
need(obs['observed_session_exit']==0 and obs['state_sha256']==statehash and state['status']=='PASS' and
     state['phase']=='complete' and len(state['records'])==1,'terminal evidence mismatch')
need(sha(RUNNER)==EXPECTED==state['runner_sha256'],'runner hash mismatch')
spec=importlib.util.spec_from_file_location('translated_audit_runner',RUNNER);r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
d,ctx,initial=r.authenticate();need(initial==state['initial'],'authenticated input drift')
rec=state['records'][0];name,declared,expected=r.CLIENTS[0];src=OUT/'src'/(name+'.lean');source=r.SOURCES[0];obj=OUT/'lib'/(name+'.olean')
need(rec['module']==name and rec['exit']==0 and sha(src)==sha(source)==r.PINS[source]==rec['source_sha256'],'source or row mismatch')
need(obj.is_file() and not obj.is_symlink() and sha(obj)==rec['object_sha256'] and rec['output_guards'][str(obj)]['sha256']==rec['object_sha256'],'object mismatch')
d.check_guard(rec['output_guards'])
for key in ('log','stderr','deps_stdout','deps_stderr'):
 p=Path(rec[key]);need(p.is_file() and sha(p)==rec[key+'_sha256'],('log mismatch',key))
need(not Path(rec['deps_stderr']).read_text(),'deps stderr not empty')
reports=r.reports(Path(rec['log']).read_text()+'\n'+Path(rec['stderr']).read_text(),expected)
need([list(x) for x in reports]==rec['axiom_reports'],'axiom report mismatch')
direct=rec['direct_inputs'];d.validate_dependencies(Path(rec['deps_stdout']).read_text().splitlines(),direct)
need(set(declared)<=set(direct) and not set(direct)-set(declared)-{'Init'},'declared imports mismatch');d.check_guard(rec['direct_guards'])
for module,entry in direct.items():
 path=Path(entry['path']);g=rec['direct_guards'].get(str(path));need(isinstance(g,dict) and g['sha256']==entry['sha256'] and path.is_file() and
       str(path.resolve())==g['realpath'] and sha(path)==entry['sha256'],('direct input mismatch',module))
 if module in ctx['prior_outputs']:
  need(path==r.PRIOR/'lib'/(module+'.olean') and g==ctx['prior_outputs'][module][str(path)],('prior route mismatch',module))
 elif module in ctx['manifest']['sources']:
  need(path==d.BASE_DIR/'lib'/(module.replace('.','/')+'.olean') and g==ctx['base']['outputs'][module][str(path)],('base route mismatch',module))
 else:
  need(any(path==root/(module.replace('.','/')+'.olean') for root in (d.PKG,d.TOOL)) and
       g==ctx['base']['guarded_companions'][str(path)],('external route mismatch',module))
for kind in ('deps','compile'):
 q=rec[kind+'_receipt'];need(q['exit']==0 and q['direct_child_reaped'] is True and q['session_drained'] is True and
     q['initial']['ppid']==obs['runner_pid'] and q['initial']['pgrp']==q['initial']['session']==q['pid'] and rec[kind+'_samples'],('owned receipt mismatch',kind))
_,_,after=r.authenticate();need(after==initial and sha(statepath)==statehash and sha(OBS)==obshash and sha(RUNNER)==EXPECTED and sha(__file__)==auditsha,'final input drift')
row={'status':'PASS_TRANSLATED_CLIENT_ARTIFACT_AUDIT','module':name,'source_sha256':rec['source_sha256'],
     'object_sha256':rec['object_sha256'],'axiom_reports':reports,'state_sha256':statehash,'outer_session_exit':obs['observed_session_exit'],
     'audit_sha256':auditsha,'scope':'One translated client and its authenticated inputs; no second Lean replay or complete transitive/dynamic ancestry.'}
with RESULT.open('x') as f:json.dump(row,f,indent=2,sort_keys=True);f.write('\n')
print(json.dumps(row,sort_keys=True))
