#!/usr/bin/env python3
"""Audit failed first-stage concrete-root compilation without Lean."""
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign17-concrete-root-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign17-concrete-root-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==29781 and o['outer_exit_code']==1 and sha(a/'state.json')==sha(out/'state.json')
s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Sign17ConcreteRoot')" and s['runner_sha256']==sha(p/'run.py')=='c4c265c67a4f626417150d88abbdbee7d940358b91812c3b5553e11f50900769';r,=s['rows'];e=json.loads((p/'source-manifest.json').read_text())['rows'][0];n='Sign17ConcreteRoot';assert r['module']==n and r['source_sha256']==e['source_sha256']==sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))
for phase in ('deps','compile'):
 x=r[phase];assert x['exit']==(0 if phase=='deps' else 1) and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];name=n+'-'+phase+'.txt';assert sha(a/name)==sha(out/name)==x['log_sha256']
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
pins={'SharingSeed17Row06':'f61a66d97ea216b92893518b77970870d465218531e9ba652ea22f08f456afb3','Sign17RootLift':'a9e50bc6101443cfadb386692232bab6b19e69d573feefc873285e20aa4727b3'}
for mod in e['imports']:
 d=r['dependencies'][mod];assert d['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][d['path']]=={'sha256':d['sha256'],'realpath':d['realpath']}
log=(a/(n+'-compile.txt')).read_text();assert log.count('error: unsolved goals')==1 and log.count('sorryAx')==1 and not (out/'lib/DiophantineConsistency'/(n+'.olean')).exists() and 'object_sha256' not in r
assert all('Sign17ConcreteRoot.'+x+'_eval' in log for x in ('shared07','shared24','shared26','shared29','shared33'))
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
print(json.dumps({'status':'PASS_FAILURE_AUDIT','outer_session':29781,'outer_exit':1,'guard_entries':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'first concrete-root stage fails; no object, concrete-gap stage or postflight'},indent=2,sort_keys=True))
