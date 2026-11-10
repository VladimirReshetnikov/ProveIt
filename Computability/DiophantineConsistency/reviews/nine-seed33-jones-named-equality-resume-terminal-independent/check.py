#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-seed33-jones-named-equality-resume-check';a=p/'attempt01';out=Path('/tmp/nine-seed33-jones-named-equality-resume-check-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='470e24856462d111e8a02cb08f7b2d29a95e5032ad93ad3a43527400c845bc76' and sha(a/'outer-result.json')=='6051c9d7f5a5c97ddce4e16cbf63bf6ba2e4328f23455235673a2a463d480a56';o=json.loads((a/'outer-result.json').read_text());assert (o['session_id'],o['exit_code'])==(14696,1)
s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Sign33MacroNamedVars')" and len(s['rows'])==1 and len(s['overlay_links'])==1388 and s['runner_sha256']==sha(p/'run.py')=='f487ee9dbd65f908186b5b714b9f92ad931cdb678dbe341de49fc795a2c20552';r,=s['rows'];e=json.loads((p/'source-manifest.json').read_text())['rows'][0];n='Sign33MacroNamedVars';assert r['module']==n and sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==r['source_sha256']==e['source_sha256'] and 'object_sha256' not in r and not (out/'lib/DiophantineConsistency'/(n+'.olean')).exists()
for ph in ('deps','compile'):
 v=r[ph];log=n+'-'+ph+'.txt';assert v['exit']==(0 if ph=='deps' else -6) and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'] and v['rss_limit_bytes']==4*1024**3 and v['host_floor_bytes']==10*1024**3 and v['timeout_seconds']==120 and sha(a/log)==sha(out/log)==v['log_sha256']
assert r['compile']['peak_session_rss_bytes']==2940456960 and 'lean::memory_exception' in (a/(n+'-compile.txt')).read_text() and "'interpreter'" in (a/(n+'-compile.txt')).read_text()
pins={'Sign33MacroVarsOutput':'d5cf436d1fe9242862a4b73037e98638bab580377f42dfa60637e6bd0ca2d8d9','Sign33NamedFormula':'ba39e705f4cc32ec52ddf0fc992d1500139f46b270bbe36cba07bddcbac1435f'}
for mod in e['imports']:
 dep=r['dependencies'][mod];assert dep['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_FAILURE_AUDIT','outer_session':14696,'compile_exit':-6,'peak_session_rss_bytes':2940456960,'scope':'first named-vars stage interpreter memory exception; no object, named equality or postflight'},indent=2))
