#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-constructor-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-forward-constructor-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'90d2364c1d5193dc53a3afac3ed108e23db42b2917f9e8740fee1f81b86c11ed','SharingForward33-compile.txt':'347cf781a22573c6fc5aec928ba5ac6d6b0cb549329bb7eee9d5a923bb4e4242','outer-observation.json':'b72b46a6062a0261764f957d1d1f631f1ed3470d313ccac03d1893033aa5fe9c'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(90019,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='SharingForward33' and r['source_sha256']=='a28cf78a396b80908dc9b00e4b1ed452bbe670d93d03de1d0a8198367b24b3ab' and r['object_sha256']=='306a8d3da4b5d24cf466f631356c4851d1a4aa2df5bb642aeb8c854cf7369e1b'
assert h(p/'src/DiophantineConsistency/SharingForward33.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/SharingForward33.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('SharingForward33-'+k+'.txt'))==x['log_sha256']
log=(a/'SharingForward33-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for t in ('witness_inputs',):assert re.search(r"'DiophantineConsistency\.SharingForward33\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
assert "'DiophantineConsistency.SharingForward33.witness_signed' depends on axioms: [propext]" in log
for mod,digest in {'DiophantineConsistency.ForwardWitness38':'085639f8f95d4929a0851b4fb2fb8abb68f1cda4a1ee8645dadbcaa92b421b6b'}.items():
 dep=r['dependencies'][mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':digest}
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1193
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':90019,'direct_guard_slots':100,'overlay_links':1193,'scope':'forward constructor coordinate projections only; no Lean replay'},sort_keys=True,indent=2))
