#!/usr/bin/env python3
"""One-row artifact audit after a failed two-client session; no Lean replay."""
import hashlib
import importlib.util
import json
from pathlib import Path
if not __debug__:raise SystemExit('refusing optimized Python')
HERE=Path(__file__).resolve().parent;TASK=HERE.parents[1];ROOT=HERE.parents[3]
RUNNER=TASK/'research/current14-structured-endpoint-coherent-runner-v3/runner.py'
RESULT=HERE/'assembly-audit-receipt.json';CLIENT=Path('/tmp/current14-structured-endpoint-coherent-v3-20261104')
EXPECTED='cf8a7b0d6df7b6c99f3eb4d9247f226c3fc0f0051fefa6dede438b2511ade349'
def need(c,m):
    if not c:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
auditsha=sha(__file__);need(not RESULT.exists(),'refusing existing audit receipt')
obs=read(HERE/'observation.json');statepath=CLIENT/'state.json';state=read(statepath);statehash=sha(statepath)
need(obs['outer_session_exit']==1 and obs['sha256']['client-state.json']==statehash and state['status']=='FAILED' and
     state['phase']=='StructuredEndpoint compile' and len(state['records'])==1,'wrong failed client state')
need(sha(RUNNER)==EXPECTED and state['runner_sha256']==EXPECTED,'runner hash mismatch')
spec=importlib.util.spec_from_file_location('v3_assembly_client',RUNNER);client=importlib.util.module_from_spec(spec);spec.loader.exec_module(client)
c,ctx,extension,initial=client.authenticate();driver=c.driver;rec=state['records'][0]
need(state['initial']==initial and rec['module']=='Current14LiteralPorts' and rec['exit']==0,'wrong assembly row')
source=CLIENT/'src/Current14LiteralPorts.lean';workspace=client.SOURCES[0];obj=CLIENT/'lib/Current14LiteralPorts.olean'
need(sha(source)==sha(workspace)==client.PINS[workspace]==rec['source_sha256'] and sha(obj)==rec['object_sha256'] and
     sha(HERE/'Current14LiteralPorts.olean.bin')==rec['object_sha256'],'assembly source or object mismatch')
for key in ('log','stderr','deps_stdout','deps_stderr'):
    path=Path(rec[key]);need(path.is_file() and sha(path)==rec[key+'_sha256'] and sha(HERE/path.name)==rec[key+'_sha256'],('assembly log mismatch',key))
need(not Path(rec['stderr']).read_text() and not Path(rec['deps_stderr']).read_text(),'assembly stderr not empty')
axioms=client.reports(Path(rec['log']).read_text(),client.CLIENTS[0][2]);need([list(x) for x in axioms]==rec['axiom_reports'],'axiom report mismatch')
lines=Path(rec['deps_stdout']).read_text().splitlines();driver.validate_dependencies(lines,rec['direct_inputs'])
need(set(rec['direct_inputs'])==set(client.CLIENTS[0][1])|{'Init'},'assembly direct imports mismatch')
driver.check_guard(rec['direct_guards']);driver.check_guard(rec['output_guards'])
for module,entry in rec['direct_inputs'].items():
    path=Path(entry['path']);guard=rec['direct_guards'].get(str(path));need(isinstance(guard,dict) and guard['sha256']==entry['sha256'] and
         path.is_file() and str(path.resolve())==guard['realpath'] and sha(path)==entry['sha256'],('direct input mismatch',module))
for kind in ('deps','compile'):
    receipt=rec[kind+'_receipt'];need(receipt['exit']==0 and receipt['session_drained'] is True and receipt['direct_child_reaped'] is True and
        len(rec[kind+'_samples'])>0,('owned receipt or samples missing',kind))
_,_,_,final=client.authenticate();need(final==initial and sha(statepath)==statehash and sha(RUNNER)==EXPECTED and sha(__file__)==auditsha,'audit evidence changed')
row={'status':'PASS_SINGLE_ASSEMBLY_ARTIFACT_AUDIT','module':rec['module'],'object_sha256':rec['object_sha256'],
     'axiom_reports':axioms,'source_sha256':rec['source_sha256'],'failed_session_exit':obs['outer_session_exit'],
     'client_state_sha256':statehash,'audit_sha256':auditsha,
     'scope':'One successful assembly row in a failed client session; no structured endpoint proof or second Lean replay.'}
with RESULT.open('x') as f:json.dump(row,f,indent=2,sort_keys=True);f.write('\n')
print(json.dumps(row,sort_keys=True))
