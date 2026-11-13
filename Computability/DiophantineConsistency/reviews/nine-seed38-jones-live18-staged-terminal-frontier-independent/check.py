#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-live18-staged-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-live18-staged-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
assert h(a/'state.json')=='26bb3423a2df282b72a2c3db443aeb4913867c5208b205a3fba8055d1ad6ba42' and h(a/'outer-terminal-author-record.json')=='0a42613ec4ad7e523a328b9b46c457fbe32c26beb24d522ef0b6b097a732715c'
o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(10769,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==4
objs=['b2c531a9eecdd13baaf18f2f130949cd8fd7602118f575cd124fffa4b0dc32dd','f028ef640af09a6477b7672e76630057147c859c26d908dafded919953f8a53c','2589ac6c78d736a31bd3e851aaa0068d43ec0a10a10b3cb648b4df8b7da9d902','d441a380efaacb979a20ed3370cfec35c900afd19d23eaa210b1b7d6bb76c143'];reports=[['d18_b_carry','d18_N_carry','d18_g_carry'],['d18_G_carry','d18_R_carry','d18_h_carry'],['d18_s_carry','d18_w_carry','d18_phi_carry'],['d18_i_carry','d18_j_carry']]
for i,(r,obj,ts) in enumerate(zip(s['rows'],objs,reports),1):
 n='Norm38MacroLive18Group%02d'%i;assert r['module']==n and r['object_sha256']==obj and h(out/'lib/DiophantineConsistency'/f'{n}.olean')==obj and h(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
 for k in ('deps','compile'):
  x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/f'{n}-{k}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
 for t in ts:assert re.search(r"'DiophantineConsistency\.Norm38MacroLive18\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 dep=r['dependencies']['DiophantineConsistency.Norm38MacroRankSymbolic'];assert dep['sha256']=='b82180e10b4cf11a375cbfdcc3087eb69985c18473ae80a9eaf99ff2e8673408' and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':dep['sha256']};assert len(r['direct_guard'])==100
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q),path
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
assert len(s['overlay_links'])==1189
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
print(json.dumps({'status':'PASS','author_recorded_outer_session':10769,'stages':4,'reports':11,'direct_guard_slots':400,'overlay_links':1189,'scope':'d18 carry equalities only; no Lean replay'},sort_keys=True,indent=2))
