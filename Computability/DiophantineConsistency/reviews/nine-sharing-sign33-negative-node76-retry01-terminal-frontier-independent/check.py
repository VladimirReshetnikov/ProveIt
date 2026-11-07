#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-negative-node76-retry01';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-negative-node76-retry01-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'80883e2565238e882f9a9dd3773313888bdee7b5d8921ccf6497c6e406bba13c','Sign33NegativeNode76-compile.txt':'f2d0f0d7e866a0f801227b62c8c7f71fd122cb2f4e36f4435fe2c17fdbf23926','outer-observation.json':'2c1e6cee472ae64387e690f6d813388bafd002e319a9310dcdc6a99f7a2dd845'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['exit_code'])==(6994,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33NegativeNode76' and r['source_sha256']=='75a9e2cbc9aae3b54c69ef488e72b24a1c531cf202715e5bf226970852e0c2dc' and r['object_sha256']=='dcea09d50e442b764ad418e791efb584b34790dd5fbaef6bc20a475cee958d8b'
assert h(p/'src/DiophantineConsistency/Sign33NegativeNode76.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33NegativeNode76.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33NegativeNode76-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33NegativeNode76-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for t in ('negative_of_core',):assert re.search(r"'DiophantineConsistency\.Sign33NegativeNode76\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,digest in {'DiophantineConsistency.Sign33StaticNode76':'7c622ce54abd71af4d2c1c38a8e9808605480ea023312f3b6ea799654a42579b','DiophantineConsistency.Sign33ReferenceNode76':'62b5b7e2edb65010dc4c4eba34aac7c6a362b6e7827129485f0dbd6458057b5c','DiophantineConsistency.Norm38ForwardGatesAssembly':'70dfab106e1db73ef99b1633f42aebab140af2cb111b58437f5b1e186f91d685','DiophantineConsistency.Norm38ForwardPrefix':'aeb6bfe74b17c695e41303bcb9f98cc5a60cb53d33774c03a84b71839d71a25f'}.items():
 dep=r['dependencies'][mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':digest}
assert len(r['direct_guard'])==250 and len(s['overlay_links'])==1196
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':6994,'direct_guard_slots':250,'overlay_links':1196,'scope':'conditional negative representative cancels node76; no Lean replay'},sort_keys=True,indent=2))
