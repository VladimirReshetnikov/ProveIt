#!/usr/bin/env python3
import hashlib,json,os,re,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-prefix-dag-composition-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign14-prefix-dag-composition-check-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==13058 and o['author_observed_numeric_outer_exit']==0 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==20 and s['runner_sha256']==sha(p/'run.py')=='598cda754c73e5fd5acc03af2e6d51f54b44930f48f41ca74729c15f39983070'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];base=json.loads((root/'research/nine-sharing-sign14-prefix-code-check/attempt01/state.json').read_text());pins={'Sign14PrefixCodeRow04':base['rows'][13]['object_sha256']};warnings=0;reports=[];guards=0
for r,e in zip(s['rows'],rows):
 n=r['module'];src=p/'src/DiophantineConsistency'/(n+'.lean');assert e['module']=='DiophantineConsistency.'+n and sha(src)==sha(out/'src/DiophantineConsistency'/(n+'.lean'))==e['source_sha256']==r['source_sha256'];assert sha(out/'lib/DiophantineConsistency'/(n+'.olean'))==r['object_sha256']
 for ph in ('deps','compile'):
  x=r[ph];name=n+'-'+ph+'.txt';assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and sha(a/name)==sha(out/name)==x['log_sha256']==o['logs'][name]
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q)
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
  guards+=1
 for mod in e['imports']:
  d=r['dependencies'][mod];assert d['sha256']==pins[mod.split('.')[-1]] and r['direct_guard'][d['path']]=={'sha256':d['sha256'],'realpath':d['realpath']}
 log=(a/(n+'-compile.txt')).read_text();assert 'error:' not in log and 'sorryAx' not in log;warnings+=log.count('warning:');assert log.count('warning:')==log.count('warning: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice');reports+=re.findall(r"'DiophantineConsistency\.Sign14PrefixDag\.(\w+_eq)' depends on axioms: \[([^]]+)\]",log);pins[n]=r['object_sha256']
expected={f'fragment{i:03}_eq' for i in range(29)}|{f'shared{i:02}Bytes_eq' for i in range(44)}|{f'row{i:02}Bytes_eq' for i in range(5)}
assert warnings==49 and len(reports)==78 and {a for a,b in reports}==expected and all(b=='propext, Classical.choice, Quot.sound' for a,b in reports)
m=json.loads((root/'research/nine-sharing-sign14-prefix-dag-fragments/manifest.json').read_text())
for e in m['fragments']:
 name=e['file']
 for q in (p/'src/DiophantineConsistency'/name,out/'src/DiophantineConsistency'/name,a/name,root/'research/nine-sharing-sign14-prefix-dag-fragments'/name):assert sha(q)==o['prefix_sha256'][name]==e['sha256'] and len(q.read_bytes())==e['length']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':13058,'stages':20,'encoding_reports':78,'warnings':warnings,'guard_entries':guards,'scope':'fragment/shared/row Code encoding equalities; long bytes/JSON/PDF remain separate'},indent=2))
