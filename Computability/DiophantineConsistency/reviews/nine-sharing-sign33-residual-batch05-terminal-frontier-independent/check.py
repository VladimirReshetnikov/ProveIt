#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-residual-batch05-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-residual-batch05-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'659fd8325cf95592f6e143d6a8af47225d62c760b243835c62279ea7083786f1','Sign33ResidualBatch05-compile.txt':'e3f8e855f526cc814e5de4d879fdfd4e3eafe8abf889c054e85a62c893a45b78','outer-observation.json':'920fd28ad00c31fe919634e28e33cf34e7697f7f37a39c4ac27bbd9b944cd48d'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['numeric_exit'])==(58665,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33ResidualBatch05' and r['source_sha256']=='0935fca1965fc7d0d6c45337404a70a8863cd1df080f1f1a8527cf4a88bef5ce' and r['object_sha256']=='9505d4fe52e0702caa501d397ff8f126db4ebc1ef8ed82b6832da0e17d55863d'
assert h(p/'src/DiophantineConsistency/Sign33ResidualBatch05.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33ResidualBatch05.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33ResidualBatch05-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33ResidualBatch05-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for t in ('row15_eval','row16_eval','row17_eval','transport_and_cuts_of_seed_zero'):assert re.search(r"'DiophantineConsistency\.Sign33ResidualBatch05\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
dep=r['dependencies']['DiophantineConsistency.SharingSign33Squares'];assert dep['sha256']=='48b6fecc8f12c80ad12ba7290a588d2d1ac36413898d07c1777c7dead0745d42' and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':dep['sha256']}
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1174
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':58665,'direct_guard_slots':100,'overlay_links':1174,'scope':'transport and two same-valuation cuts with casts; no Lean replay'},sort_keys=True,indent=2))
