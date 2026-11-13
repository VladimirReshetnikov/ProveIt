#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-current-natural-core-norms-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-current-natural-core-norms-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'f0d666474d850def450411c2007eb2d8d57329709b5450aee08a501004fef086','Sign33CurrentNaturalCoreNorms-compile.txt':'b7d63741e0142166194f677da477cd48744e56d6d933f378f3bbd975380ce65a','outer-observation.json':'a06ca6fa432827c67aae3cb350d3adcdacfd455996c55c57b8717dd3526e9b09'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['exit_code'])==(27566,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33CurrentNaturalCoreNorms' and r['source_sha256']=='d977d8b81971154b27f58da6f61fd0ccb2795aff0f273504a7f94aed66a87b35' and r['object_sha256']=='07ddb5120d90585c4f86147aa3e8d388f5999356c2938ff8782513489f077c02'
assert h(p/'src/DiophantineConsistency/Sign33CurrentNaturalCoreNorms.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33CurrentNaturalCoreNorms.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33CurrentNaturalCoreNorms-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33CurrentNaturalCoreNorms-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for t in ('natural_source_core_norms',):assert re.search(r"'DiophantineConsistency\.Sign33CurrentNaturalCoreNorms\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,digest in {'DiophantineConsistency.Sign33CurrentCoreNorms':'494d28f41ea9767d30216bfe5dd4e13026fb10d89cc1559b9ec8d4c8bee62d49'}.items():
 dep=r['dependencies'][mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':digest}
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1195
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':27566,'direct_guard_slots':100,'overlay_links':1195,'scope':'current natural source zero implies shifted core norms; no Lean replay'},sort_keys=True,indent=2))
