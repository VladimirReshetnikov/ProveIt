#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-group03-positive-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-forward-group03-positive-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'27cde04c2415fc6d5728da8430b2ee55f140dfb200440fa26bbd796c3ce68152','Sign33ForwardGroup03Positive-compile.txt':'5959b11af11205da44fb7086b5232a2204e51e64952705f4a6bbc86b83ae7d8a','outer-observation.json':'f41d6c45e1cd77c219214423148f89363bf6c409da7a7bdeb18dd297d826c495'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(73233,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33ForwardGroup03Positive' and r['source_sha256']=='e02d67ef01e58d92d65ab643991d00e7dcc63079308279b81d6ff6330dd4230e' and r['object_sha256']=='3c9c631307cb74d4ca716fbd5867ab67eb6978122f13434c7f51c33d30e4885e'
assert h(p/'src/DiophantineConsistency/Sign33ForwardGroup03Positive.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33ForwardGroup03Positive.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33ForwardGroup03Positive-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33ForwardGroup03Positive-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for t in ('constructor_cuts',):assert re.search(r"'DiophantineConsistency\.Sign33ForwardGroup03Positive\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,digest in {'DiophantineConsistency.SharingForward33':'306a8d3da4b5d24cf466f631356c4851d1a4aa2df5bb642aeb8c854cf7369e1b','DiophantineConsistency.Sign33ResidualAssembly':'0306acc92c2199a99d58eb54ce6f78787e61beb2ddb1595d9aaeb36d10a4bef8'}.items():
 dep=r['dependencies'][mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':digest}
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1194
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':73233,'direct_guard_slots':150,'overlay_links':1194,'scope':'two positive forward cut equations only; no Lean replay'},sort_keys=True,indent=2))
