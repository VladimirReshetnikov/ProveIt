#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-prefix-dag-lemma-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign14-prefix-dag-lemma-check-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==55499 and o['author_observed_numeric_outer_exit']==0 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1 and s['runner_sha256']==sha(p/'run.py')=='0d1278024ffb35922d22002ccfc1058d2f8f272632d4d19c321c2f36c35c7e14'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];r,=s['rows'];n='Sign14PrefixDagShared07';src=p/'src/DiophantineConsistency'/(n+'.lean');assert e['module']=='DiophantineConsistency.'+n and sha(src)==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==e['source_sha256']==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']
for ph in ('deps','compile'):
 x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']==o['logs'][name]
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
base=json.loads((root/'research/nine-sharing-sign14-prefix-code-check/attempt01/state.json').read_text());assert e['imports']==['DiophantineConsistency.Sign14PrefixCodeRow00'];d=r['dependencies'][e['imports'][0]];assert d['sha256']==base['rows'][9]['object_sha256'] and r['direct_guard'][d['path']]=={'sha256':d['sha256'],'realpath':d['realpath']}
log=' '.join((a/(n+'-compile.txt')).read_text().split());assert 'Sign14PrefixDagShared07.shared07_fragment' in log and log.count('[propext, Classical.choice, Quot.sound]')==1 and all(t not in log for t in ('error:','warning:','sorryAx'))
for q in (p/'src/DiophantineConsistency/fragment007.prefix',out/'src/DiophantineConsistency/fragment007.prefix',root/'research/nine-sharing-sign14-prefix-dag-fragments/fragment007.prefix'):assert len(q.read_bytes())==15 and sha(q)==o['prefix_sha256']=='0c20087a3433dde1bd4f2b39fbc01b9a1d6789cd90aa49fa83a0d48bd8eabddb'
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':55499,'stages':1,'scope':'15-byte subtree-aligned shared07 fragment, external full-row reconstruction only'},indent=2))
