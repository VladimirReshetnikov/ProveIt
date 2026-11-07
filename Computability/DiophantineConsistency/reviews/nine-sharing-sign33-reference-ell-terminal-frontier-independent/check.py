#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-reference-ell-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-reference-ell-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'55e40338fc8a1c4274b7a53aa696c4a03eb7382c22b949fb3eec82ec9a916c0d','Sign33ReferenceEll-compile.txt':'b852e21fb9ac9c715e684b795c426c093fee794a3f009689e3f07beedacb23c4','outer-observation.json':'1a94dc20bc0ca682f75813f05a1335397d7bc62f7e724053ee10a740546bf993'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['exit_code'])==(63509,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33ReferenceEll' and r['source_sha256']=='de77993a9c692389f563cfde2b1b405b19cfd7ebb2765ae26d34739751de4976' and r['object_sha256']=='0bc514b3781c16434a3360dd905fa32b0711491713f5b234f0dff0c482e9696d'
assert h(p/'src/DiophantineConsistency/Sign33ReferenceEll.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33ReferenceEll.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33ReferenceEll-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33ReferenceEll-compile.txt').read_text();assert log.count('warning:')==1 and 'error:' not in log and 'sorryAx' not in log
for t in ('reference_ell',):assert re.search(r"'DiophantineConsistency\.Sign33ReferenceEll\."+t+r"' depends on axioms: \[propext\]",log)
for mod,digest in {'DiophantineConsistency.Norm38ReferenceFieldsAll':'3f7e3aea0ca0fa2c9700d128fd6d3a563a2345a0d61b81bcd0d87478c98b2dfd'}.items():
 dep=r['dependencies'][mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':digest}
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1194
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':63509,'direct_guard_slots':100,'overlay_links':1194,'scope':'generic commutative ring reference node 30 equals ell; no Lean replay'},sort_keys=True,indent=2))
