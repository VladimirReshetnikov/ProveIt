#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-ring-gates01-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-ring-gates01-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'2d1bfc380e2f75d073f4f89f85ff1eb72fc45ffc9076be6cdd370b1a6fc7fbaf','Sign33RingGates01-compile.txt':'e7ecb30bea97f14b5484e211af91c846aad34fff0b5866e95f3782e29f3e947e','outer-observation.json':'28857d0dad6e5fff7474e89cc4b18b01d18684eaa7ce1965ccc19afc85f88ef2'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(31421,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33RingGates01' and r['source_sha256']=='72a0e785ebb71b7caaabdc9609afef9a9b7fd87b2e92f4b12e20b4a324009ea9' and r['object_sha256']=='01cc7e86655f982821f62391b48a0a21455baf2d2565ee7b5ea793519d714086'
assert h(p/'src/DiophantineConsistency/Sign33RingGates01.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33RingGates01.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33RingGates01-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33RingGates01-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for t in ('gate24','gate25','gate26'):assert re.search(r"'DiophantineConsistency\.Sign33RingGates01\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,sha in {'Sign33Lift38':'d7ee70d844f40e513e35302eee58eb1de707829b8bd288ba3328284b05aedda3','NormAssignment38':'74e28c7b054f593b9949a707cb156a45065594af202639b49941492545dc5de1'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==sha and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':sha}
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1193
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':31421,'direct_guard_slots':150,'overlay_links':1193,'scope':'three ring-value gate equations; no Lean replay'},sort_keys=True,indent=2))
