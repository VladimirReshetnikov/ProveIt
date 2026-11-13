#!/usr/bin/env python3
"""Inspect current-beta retry receipt and direct provider without Lean."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign20-current-beta-retry-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign20-current-beta-retry-20261109');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
o=json.loads((a/'outer-result.json').read_text());assert o['outer_session']==95995 and o['outer_exit_code']==0
assert sha(a/'state.json')==sha(out/'state.json');s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and s['runner_sha256']==sha(p/'run.py')=='8e9abac5facbeb2a4c15a6a594063c8d5dcc0e703a052a79a05cf608c446d274'
r,=s['rows'];e,=json.loads((p/'source-manifest.json').read_text())['rows'];n='Sign20CurrentBeta';assert r['module']==n and r['source_sha256']==e['source_sha256']==sha(p/'src/DiophantineConsistency'/(n+'.lean'))==sha(out/'src/DiophantineConsistency'/(n+'.lean'))
assert r['object_sha256']==sha(out/'lib/DiophantineConsistency'/(n+'.olean'))=='e4c29037e8e76ee4bae08c7d9b85286af83cde7862174d84b4bce0297477ac36'
for phase in ('deps','compile'):
 x=r[phase];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];log=n+'-'+phase+'.txt';assert sha(a/log)==sha(out/log)==x['log_sha256']
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
d=r['dependencies']['DiophantineConsistency.Sign20CurrentExpressionDef'];assert d['sha256']=='325ed61a2f8d6f4af8516240f782f83d5ca83579c8184a7fad5dc066d02f96a3' and r['direct_guard'][d['path']]=={'sha256':d['sha256'],'realpath':d['realpath']}
log=' '.join((a/(n+'-compile.txt')).read_text().split());assert not any(x in log for x in ('warning:','error:','sorryAx'))
for th in ('positive','nonzero'):assert "'DiophantineConsistency.Sign20CurrentBeta."+th+"' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
subprocess.run([sys.executable,'-I','-S','-B',str(p/'expression-survey.py')],check=True,capture_output=True,timeout=120)
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':95995,'outer_exit':0,'guard_entries':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'current symbolic port 0 is positive and nonzero; no external byte binding'},indent=2,sort_keys=True))
