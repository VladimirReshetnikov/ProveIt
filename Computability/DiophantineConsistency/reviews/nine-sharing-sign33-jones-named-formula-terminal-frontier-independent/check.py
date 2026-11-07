#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-jones-named-formula-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-jones-named-formula-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'f9ed7a8e03b6458d4fef44370059d192a95bff3db6b2d12127dce16a17081964','Sign33NamedFormula-compile.txt':'2445667cadf08eabe6d84750f93e9e5497c0132436858314917265af66cf7659','outer-observation.json':'a11a6818c39e814beceb7d18f339373787d71a91d8fec60c6334f38218def4aa'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['exit_code'])==(5917,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33NamedFormula' and r['source_sha256']=='297573ea8e44e9047b73614337f2c0054fcc9de1c42272a4893bf6365d7e2871' and r['object_sha256']=='ba39e705f4cc32ec52ddf0fc992d1500139f46b270bbe36cba07bddcbac1435f'
assert h(p/'src/DiophantineConsistency/Sign33NamedFormula.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33NamedFormula.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33NamedFormula-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33NamedFormula-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for t in ('eval_current',):assert re.search(r"'DiophantineConsistency\.Sign33NamedFormula\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,digest in {'DiophantineConsistency.Sign33IPRAEndpoint':'a6fa32adea62053f1ad4e1d0db809171dd2881e8eacefbba6a43ce5ab21fd80c','DiophantineConsistency.ModelJonesSyntax':'ca320ae03c5aece08482a0eb125d58c12d371ce524cce685428b0550a96c5171'}.items():
 dep=r['dependencies'][mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':digest}
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1267
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':5917,'direct_guard_slots':150,'overlay_links':1267,'scope':'ring-generic symbolic named Jones RHS evaluation; no Lean replay'},sort_keys=True,indent=2))
