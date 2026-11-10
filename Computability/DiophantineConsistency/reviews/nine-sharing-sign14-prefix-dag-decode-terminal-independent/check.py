#!/usr/bin/env python3
import hashlib,json,os,re,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];p=root/'research/nine-sharing-sign14-prefix-dag-decode-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign14-prefix-dag-decode-check-20261110');sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();o=json.loads((a/'outer-result.json').read_text());assert o['author_observed_outer_session']==13345 and o['author_observed_numeric_outer_exit']==0 and sha(a/'state.json')==sha(out/'state.json')==o['state_sha256'];s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==5 and s['runner_sha256']==sha(p/'run.py')=='2c3bbc1e88ba209cfd5960ceb307ad29983ec82329352f7597508382c65e28c0'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];base=json.loads((root/'research/nine-sharing-sign14-prefix-dag-composition-check/attempt01/state.json').read_text());pins={'Sign14PrefixDagRow04':base['rows'][19]['object_sha256']};warnings=0;reports=[];guards=0
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
 log=(a/(n+'-compile.txt')).read_text();assert 'error:' not in log and 'sorryAx' not in log;warnings+=log.count('warning:');reports+=re.findall(r"'DiophantineConsistency\.Sign14PrefixDagDecode\.(\w+)' depends on axioms: \[([^]]+)\]",' '.join(log.split()));pins[n]=r['object_sha256']
expected={f'row{i:02}_{k}' for i in range(5) for k in ('depth','decode')};assert warnings==0 and len(reports)==10 and {a for a,b in reports}==expected and all(b in ('propext','propext, Classical.choice, Quot.sound') for a,b in reports)
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
print(json.dumps({'status':'PASS_TERMINAL_AUDIT','outer_session':13345,'stages':5,'decode_reports':10,'warnings':warnings,'guard_entries':guards,'scope':'five embedded fragment-DAG lists decode to staged rows; original file/JSON/PDF relation remains external'},indent=2))
