#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-residual-assembly-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-residual-assembly-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'689fe69a26c9315785321d7fa1fcf37472fb42380540860e201d94ac98762ca9','Sign33ResidualAssembly-compile.txt':'dfb1eced19eb3e72a26e065b506122864fb19cd7faa6b95387480e7cbb59fb12','outer-observation.json':'50aaea15e3ce324a912ec21204cae2abc272072604044f92d344766d48643bb9'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(22755,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33ResidualAssembly' and r['source_sha256']=='da9229b543500e40d4a3d5fa100fe11a969b58bcdc4f280d385abf3617ba2358' and r['object_sha256']=='0306acc92c2199a99d58eb54ce6f78787e61beb2ddb1595d9aaeb36d10a4bef8'
assert h(p/'src/DiophantineConsistency/Sign33ResidualAssembly.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33ResidualAssembly.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33ResidualAssembly-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33ResidualAssembly-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log and re.search(r"'DiophantineConsistency\.Sign33ResidualAssembly\.all_cuts_of_seed_zero' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
objects=['b50a018d85c5d6939cfc6025bcac5612d01b2e3c2570d3780725a708ebe92cc7','de360ead8b07e8b770029067431decacd8323e56d1b4870b5b1333ed077c1f5b','bae92aa8c5fbb599205cd75c4848ff45d474188eee6f34e4b7e867589b4fe2b0','63cd9e3752c33243326e16f99015e247b2f15f223ca740c74d0fc17ab6bc59c5','ebfab8778a83272454b7aa164b22e02d5aad1070dcab389001854a41d3adb829','9505d4fe52e0702caa501d397ff8f126db4ebc1ef8ed82b6832da0e17d55863d','3cf0a657954b0c53bb61c11e2a090069a63567f610826a0be23885b320ec2722','b31aafb38c8892ae24e459edc57b1a7cd32ea932392bc6733fecdc12a2e16c40']
for i,sha in enumerate(objects):
 dep=r['dependencies']['DiophantineConsistency.Sign33ResidualBatch%02d'%i];assert dep['sha256']==sha and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':sha}
assert len(r['direct_guard'])==450 and len(s['overlay_links'])==1182
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':22755,'direct_guard_slots':450,'overlay_links':1182,'scope':'one-way same-valuation 24-consequence assembly; no Lean replay'},sort_keys=True,indent=2))
