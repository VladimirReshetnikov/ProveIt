#!/usr/bin/env python3
"""Artifact cross-check after an observed successful v3 extension session."""
import collections
import hashlib
import importlib.util
import json
import os
import re
import sys
from pathlib import Path
if not __debug__:raise SystemExit('refusing optimized Python')
HERE=Path(__file__).resolve().parent;TASK=HERE.parents[1]
PACKET=TASK/'research/current14-structured-endpoint-coherent-runner-v3'
RUNNER=PACKET/'runner.py';RESULT=HERE/'receipt.json';OBS=PACKET/'extension-terminal-observation.json'
SUP=Path('/tmp/current14-printed-port-coordinator-supervisor-v3-20261104/receipt.json')
EXPECTED_RUNNER='cf8a7b0d6df7b6c99f3eb4d9247f226c3fc0f0051fefa6dede438b2511ade349'
def need(c,m):
    if not c:raise ValueError(m)
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def read(p):return json.loads(Path(p).read_text())
def guard(g):
    for name,expected in g.items():
        p=Path(name)
        if expected is None:need(not os.path.lexists(p),('unexpected companion',name))
        else:need(p.is_file() and str(p.resolve())==expected['realpath'] and sha(p)==expected['sha256'],('guard mismatch',name))
audit_sha=sha(__file__)
need(not RESULT.exists(),'refusing existing audit receipt')
need(OBS.is_file() and SUP.is_file(),'missing observed supervisor terminal evidence')
obs=read(OBS);obshash=sha(OBS);sup=read(SUP)
need(obs.get('observed_session_exit')==0 and obs.get('supervisor_receipt_sha256')==sha(SUP) and sup.get('status')=='PASS' and sup.get('child_exit')==0,
     'supervisor session or child did not pass')
need(sha(RUNNER)==EXPECTED_RUNNER,'reviewed client runner changed')
spec=importlib.util.spec_from_file_location('v3_terminal_client',RUNNER);client=importlib.util.module_from_spec(spec);spec.loader.exec_module(client)
c,ctx,ext,initial=client.authenticate();driver=c.driver;project=driver.OUT/'lib';records=ext['records'];outputs=ext['outputs']
need(len(records)==len(ctx['order'])==61 and [x['module'] for x in records]==ctx['order'], 'extension rows mismatch')
counts=collections.Counter();direct_edges=0
for index,rec in enumerate(records):
    name=rec['module'];row=ctx['rows'][name];source=driver.OUT/'src'/(name.replace('.','/')+'.lean');workspace=driver.ROOT/row['workspace_path']
    need(rec['exit']==0 and sha(source)==sha(workspace)==row['sha256']==rec['source_sha256'],('source or exit mismatch',name))
    obj=project/(name.replace('.','/')+'.olean');out=outputs[name]
    need(obj.is_file() and not obj.is_symlink() and sha(obj)==rec['object_sha256'] and out[str(obj)]['sha256']==rec['object_sha256'],('output mismatch',name))
    guard(out)
    log=Path(rec['log']);need(log==driver.OUT/'logs'/(f'{index:03d}-'+name.replace('.','_')+'.log') and sha(log)==rec['log_sha256'],('log mismatch',name))
    need(not re.search(r'(?m)^.*(?:error:|error\([^)]*\):)|\bsorryAx\b|\bsorry\b',log.read_text()),('error or sorry pattern',name))
    direct=rec['direct_inputs'];declared=set(row['imports']);need(declared<=set(direct) and not set(direct)-declared-{'Init'},('declared imports mismatch',name))
    depbase=driver.OUT/'logs'/(f'{index:03d}-'+name.replace('.','_')+'.deps')
    depout=Path(str(depbase)+'.stdout');deperr=Path(str(depbase)+'.stderr')
    need(rec['deps_stdout']==str(depout) and rec['deps_stderr']==str(deperr) and sha(depout)==rec['deps_stdout_sha256'] and
         sha(deperr)==rec['deps_stderr_sha256'] and not deperr.read_bytes(),('deps log mismatch',name))
    lines=depout.read_text().splitlines();by_path={v['path']:k for k,v in direct.items()}
    need(len(by_path)==len(direct) and set(lines)==set(by_path),('deps/direct paths mismatch',name))
    occurrences=collections.Counter(lines)
    for path,count in occurrences.items():
        module=by_path[path];need(count in (1,2) if module=='Init' else count==1,('dependency multiplicity mismatch',name,module,count))
        if module=='Init':counts[count]+=1
    for module,entry in direct.items():
        direct_edges+=1;path=Path(entry['path'])
        if module in ctx['manifest']['sources']:
            expected=project/(module.replace('.','/')+'.olean');sourceguard=ext['base_overlay_guards']
            need(entry['kind']=='project' and path==expected,('base route mismatch',name,module))
        elif module in ctx['rows']:
            expected=project/(module.replace('.','/')+'.olean');sourceguard=outputs[module]
            need(entry['kind']=='project' and path==expected,('fresh route mismatch',name,module))
        else:
            roots={'package':driver.PKG,'toolchain':driver.TOOL};need(entry['kind'] in roots,'unknown external route')
            need(path==roots[entry['kind']]/(module.replace('.','/')+'.olean'),('external route mismatch',name,module));sourceguard=ext['external_guards']
        g=sourceguard.get(str(path));need(isinstance(g,dict) and g['sha256']==entry['sha256'] and
            path.is_file() and str(path.resolve())==g['realpath'] and sha(path)==entry['sha256'],('direct producer mismatch',name,module))
    for kind in ('deps','compile'):
        q=rec[kind+'_receipt'];need(q['exit']==0 and q['session_drained'] is True and q['direct_child_reaped'] is True,('process receipt mismatch',name,kind))
guard(ext['base_overlay_guards']);guard(ext['external_guards']);guard(ext['overlay_external_guards'])
for g in outputs.values():guard(g)
_,_,_,final=client.authenticate();need(final==initial,'extension authentication changed during audit')
need(sha(OBS)==obshash and obs['supervisor_receipt_sha256']==sha(SUP),'terminal evidence changed')
need(sha(__file__)==audit_sha and sha(RUNNER)==EXPECTED_RUNNER,'audit or client runner changed during audit')
row={'status':'PASS_SINGLE_EXTENSION_ARTIFACT_AUDIT','rows':61,'direct_edges':direct_edges,'init_multiplicity_counts':dict(counts),
     'initial':initial,'outer_session_exit':obs['observed_session_exit'],'audit_sha256':audit_sha,
     'scope':'Artifact cross-check and reviewed verifier reuse, not a second Lean replay or full transitive/dynamic ancestry authentication.'}
with RESULT.open('x') as f:json.dump(row,f,indent=2,sort_keys=True);f.write('\n')
print(json.dumps(row,sort_keys=True))
