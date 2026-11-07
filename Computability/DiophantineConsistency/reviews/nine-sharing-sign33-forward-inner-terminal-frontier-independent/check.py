#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-inner-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-forward-inner-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'e21f1ef801c65a111bbf1a360cdff6c1bf003cbf6ce529a925c57fd270ad2d8a','Sign33ForwardInner-compile.txt':'34b8651ba06e63774f2490877a7ae73e2ea5b32fd8664fb732269ff208604147','outer-observation.json':'1bbfd2a498f5155434ef4b4c391434f63a0b23a76c8dd722e9118b50691904cd'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['exit_code'])==(90798,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33ForwardInner' and r['source_sha256']=='82ccb5424f22e331daf55f08abaaa23825637abb0b7209eed7b6e50322263ee0' and r['object_sha256']=='313751eff9ff9cf5f760f1b40681eabd71f403377afa3229e84ed80530c86b88'
assert h(p/'src/DiophantineConsistency/Sign33ForwardInner.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33ForwardInner.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33ForwardInner-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33ForwardInner-compile.txt').read_text();assert log.count('warning:')==2 and 'error:' not in log and 'sorryAx' not in log
for t in ('inner_of_core',):assert re.search(r"'DiophantineConsistency\.Sign33ForwardInner\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,digest in {'DiophantineConsistency.SharingForward33':'306a8d3da4b5d24cf466f631356c4851d1a4aa2df5bb642aeb8c854cf7369e1b','DiophantineConsistency.Sign33ResidualAssembly':'0306acc92c2199a99d58eb54ce6f78787e61beb2ddb1595d9aaeb36d10a4bef8','FreshModel106':'d18cea14c5bf1a363aac4fbc76a9afa72623a4df185eba25070112c514deb942'}.items():
 dep=r['dependencies'][mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':digest}
assert len(r['direct_guard'])==200 and len(s['overlay_links'])==1194
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':90798,'direct_guard_slots':200,'overlay_links':1194,'scope':'conditional forward inner cut only; no Lean replay'},sort_keys=True,indent=2))
