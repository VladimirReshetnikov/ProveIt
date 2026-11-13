#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-forward-norm-p-retry02';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-forward-norm-p-retry02-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'04830736f5a36388f9daafe92232587f8baec4b265db021ce256b5a15a8adffa','Sign33ForwardNormP-compile.txt':'b72cf0459724c2b180373faf685488dc6e818e6888be8e00c71f4e34d37c9da6','outer-observation.json':'6219b79d85466f1c9d42ac42ed82c79c28d076f03c66b5fd3f7e4eefa293eabe'}.items():assert h(a/n)==v
o=json.loads((a/'outer-observation.json').read_text());assert (o['session_id'],o['exit_code'])==(87401,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Sign33ForwardNormP' and r['source_sha256']=='53ca289ae6f0dc79b03cc5072bd3b45bcc57f561988afefe991209bf7f710c3f' and r['object_sha256']=='7629f71fdaf8976674ca2650e9137e80f38367d0653a027cb53731e6ecdd2726'
assert h(p/'src/DiophantineConsistency/Sign33ForwardNormP.lean')==r['source_sha256'] and h(out/'lib/DiophantineConsistency/Sign33ForwardNormP.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/('Sign33ForwardNormP-'+k+'.txt'))==x['log_sha256']
log=(a/'Sign33ForwardNormP-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for t in ('norm_p_of_core',):assert re.search(r"'DiophantineConsistency\.Sign33ForwardNormP\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,digest in {'DiophantineConsistency.Sign33ConstructorEllRetry':'be7375726277bf550e39cfd39b20955b120c6febd748362e1a269c46072ad830'}.items():
 dep=r['dependencies'][mod];assert dep['sha256']==digest and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':digest}
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1200
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
assert (a/'survey-before.json').read_bytes()==(a/'survey-after.json').read_bytes()
print(json.dumps({'status':'PASS','author_recorded_outer_session':87401,'direct_guard_slots':100,'overlay_links':1200,'scope':'conditional P and tau representative implies constructor P field; no Lean replay'},sort_keys=True,indent=2))
