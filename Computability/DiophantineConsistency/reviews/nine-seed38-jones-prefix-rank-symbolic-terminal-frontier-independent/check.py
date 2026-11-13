#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-prefix-rank-symbolic-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-prefix-rank-symbolic-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
assert h(a/'state.json')=='57241eb4033b3c8208161ad45b34ae566c97d29a094de17239c552ce985fbdef' and h(a/'outer-terminal-author-record.json')=='38841db2b76089e5b3561eacec8ce2a7fa8158c40c8a7a670ba7d8a9169b27b1'
o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(36172,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==3
names=['Norm38MacroRankValuesSums','Norm38MacroRankValuesOther','Norm38MacroRankSymbolic'];objects=['a6f82ed8846e1080a8a51de9248c87fd60c050c2ba541320148b85deb403120d','722fa848f555e142b7f5a37844f345f5c15069f9678fd1144af3ce3bf2680917','b82180e10b4cf11a375cbfdcc3087eb69985c18473ae80a9eaf99ff2e8673408'];reports=[['d10_e_value','d10_ell_value','d10_lambda_value'],['d10_b_value','d10_g_value','d10_theta_value'],['d11_rank_symbolic']]
expected=[{'Norm38MacroRankComposition':'682aefdc3bde128ef02c981a75c84230ade20e306cfadefd3f49f99fe7bcb548','Norm38MacroPrefixE':'b1742d0c3c6372d05c31627da4e6f4bc32ad1757a7d20c1e31774109ec3cbe64','Norm38MacroPrefixEll':'bdf292db45b95d08a08d93a886567f773c0462c16bed0a6a8806a7e3b7539712','Norm38MacroPrefixLambda':'7f2d141c3f7c256e86f61f7ddef52f5a6025ce872a5ede3d3c1f5f8fd4caba0d'},{'Norm38MacroRankValuesSums':objects[0],'Norm38MacroPrefixGsmall':'dd500df7b9ea630528181ee3e1ac62f955822471a9f3385e0a833c13758dbaf2','Norm38MacroPrefixTheta':'6c76ea5f4ab7a4390bad1fd78c54fd95353d23af842596a0823d72d8fb088a64'},{'Norm38MacroRankValuesOther':objects[1]}]
for i,(r,n,obj,ts,ex) in enumerate(zip(s['rows'],names,objects,reports,expected)):
 assert r['module']==n and r['object_sha256']==obj and h(out/'lib/DiophantineConsistency'/f'{n}.olean')==obj and h(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
 for k in ('deps','compile'):
  x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/f'{n}-{k}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
 for t in ts:assert re.search(r"'DiophantineConsistency\.[^']*\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 for mod,sha in ex.items():
  dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==sha and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':sha}
 assert len(r['direct_guard'])==[250,200,100][i]
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q),path
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
assert len(s['overlay_links'])==1186
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
print(json.dumps({'status':'PASS','author_recorded_outer_session':36172,'stages':3,'reports':7,'direct_guard_slots':550,'overlay_links':1186,'scope':'symbolic d11 short prefix; no Lean replay'},sort_keys=True,indent=2))
