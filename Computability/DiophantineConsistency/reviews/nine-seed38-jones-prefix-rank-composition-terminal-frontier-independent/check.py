#!/usr/bin/env python3
import hashlib,json,os
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-prefix-rank-composition-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-prefix-rank-composition-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'a8cec56c00f57638276c1b48f9723f13da74904c5c76d4746b8af5ad2b4b7bbb','Norm38MacroRankComposition-compile.txt':'40ac73a13b60ab7a465070e15ce707752e3f94468eda674c1c1f838222fb087b','outer-terminal-author-record.json':'e91c253a689865121cd8914c09050b4ad205fed55250456e75bfeda2603fc312'}.items():assert h(a/n)==v
o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(33017,1)
s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Norm38MacroRankComposition' and 'object_sha256' not in r and not (out/'lib/DiophantineConsistency/Norm38MacroRankComposition.olean').exists()
assert r['source_sha256']=='7456d37335417d1aec5cf8ed97d1d1cb9eaa117d27f5a8a04fb945dbab3771ca' and h(p/'src/DiophantineConsistency/Norm38MacroRankComposition.lean')==r['source_sha256'];assert r['deps']['exit']==0 and r['compile']['exit']==1 and r['compile']['stop_reason'] is None
for k in ('deps','compile'):assert not r[k]['monitor_errors'] and not r[k]['observed_descendant_pids'] and h(a/('Norm38MacroRankComposition-'+k+'.txt'))==r[k]['log_sha256']
log=(a/'Norm38MacroRankComposition-compile.txt').read_text();assert 'unsolved goals' in log and '(Fin.last 0).castSucc' in log and 'sorryAx' in log
for n,sha in {'Norm38MacroRankCodeLink':'5a200be6ed07ad99ee680339c8a6383f4140f586fb1dcb311ad4e7eea1557259','Norm38MacroPrefixBPower':'e66a9ddbe1f06f6d2e593939a077494517f7351731ed41106eb23645fd26b27b'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+n];assert dep['sha256']==sha and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':sha}
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1185
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
print(json.dumps({'status':'PASS_FAILURE_AUDIT','author_recorded_outer_session':33017,'direct_guard_slots':150,'overlay_links':1185,'scope':'unsolved index goal, no successful object or Lean replay'},sort_keys=True,indent=2))
