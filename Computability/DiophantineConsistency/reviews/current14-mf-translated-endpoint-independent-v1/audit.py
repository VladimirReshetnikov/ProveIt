#!/usr/bin/env python3
"""Read-only pins/previous-producer and synthetic controls audit; no Lean."""
import hashlib,importlib.util,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B without -O')
root=Path(__file__).resolve().parents[2];p=root/'research/current14-mf-translated-endpoint';prior=Path('/tmp/current14-mf-base-only-attempt02-20261104')
def sha(f):return hashlib.sha256(Path(f).read_bytes()).hexdigest()
pins={'runner.py':'8ce9ef6199d5dc9b4d51f2666fac75b8a934692f261bfede177b64668b1aee9a','TranslatedEndpointMF.lean':'55dc65a31ea0c36927544317485eecb59e4e6e702c3067715da2a2f1241c4f8d','controls.py':'f9e60b5087fe06beada2a474672cf6ad29a884efe2a08272e4a86ba3a0d8fa15','controls-receipt.json':'356237de1c3911681ce3b5f036ab29ee9efa6e8ee6d50ecac1f17ce50d42a6f6'}
for n,h in pins.items():
 if sha(p/n)!=h:raise RuntimeError('packet pin '+n)
r=json.loads((p/'controls-receipt.json').read_text())
if r['status']!='PASS' or len(r['runs'])!=2 or any(x['exit']!=0 or x['stderr'] for x in r['runs']):raise RuntimeError('controls receipt failure')
if any(sha(p/n)!=h for n,h in r['pins_sha256'].items()):raise RuntimeError('receipt source pin mismatch')
if json.loads(r['runs'][0]['stdout'])['status']!='PASS' or json.loads(r['runs'][1]['stdout'])['status']!='PREFLIGHT_PASS':raise RuntimeError('prior controls result')
spec=importlib.util.spec_from_file_location('translated_runner_review',p/'runner.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);mod.pin()
if len(mod.PINS)!=13 or mod.OUT.exists():raise RuntimeError('pin count/output is not fresh')
state=json.loads((prior/'state.json').read_text());rows=state['records']
if state['status']!='PASS' or state['phase']!='complete' or [x['module'] for x in rows]!=['Current14LiteralPortsMF','StructuredEndpointMF']:raise RuntimeError('prior terminal rows')
for row in rows:
 if row['exit']!=0 or sha(prior/'lib'/(row['module']+'.olean'))!=row['object_sha256']:raise RuntimeError('prior object')
 for key in ('deps_receipt','compile_receipt'):
  c=row[key]
  if c['exit']!=0 or not c['direct_child_reaped'] or not c['session_drained']:raise RuntimeError('prior child receipt')
 for key in ('log','stderr','deps_stdout','deps_stderr'):
  if sha(row[key])!=row[key+'_sha256']:raise RuntimeError('prior log mismatch')
obs=json.loads((root/'research/current14-mf-base-only-endpoint-attempt02/terminal-observation.json').read_text());aud=json.loads((root/'reviews/current14-mf-base-only-attempt02-terminal/receipt.json').read_text())
if obs['observed_session_exit']!=0 or obs['state_sha256']!=sha(prior/'state.json') or aud['state_sha256']!=obs['state_sha256'] or aud['status']!='PASS_RECORDED_CLIENT_ROWS_ARTIFACT_AUDIT':raise RuntimeError('prior outer/audit mismatch')
controls=subprocess.run([sys.executable,'-I','-S','-B',str(p/'controls.py')],capture_output=True,text=True,check=True,timeout=20)
if controls.stderr or json.loads(controls.stdout)['status']!='PASS':raise RuntimeError('fresh synthetic controls')
print(json.dumps({'status':'PASS_STATIC_REVIEW','source_pins':pins,'runner_pins_checked':len(mod.PINS),'prior_rows':len(rows),'prior_outer_exit':0,'output_path_absent':True,'synthetic_controls':'PASS','scope':'No Lean or client runner launched; transitive and dynamic provider ancestry inherited.'},sort_keys=True))
