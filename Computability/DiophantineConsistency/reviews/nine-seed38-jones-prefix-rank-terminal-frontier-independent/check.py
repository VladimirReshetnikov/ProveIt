#!/usr/bin/env python3
import hashlib,json,os
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-prefix-rank-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-prefix-rank-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'state.json':'c96300d1250ab2301b108456e29c96f05570bada97aff5d15f061355fd6502f6','Norm38MacroRankRaw-compile.txt':'94647a42b9f6ba17ea49b26e4abe80fcdc41a2b35fcf44f3dc5e3e46383bb34d','outer-terminal-author-record.json':'c8486cb967384b71d964be0f2fcb958aea9480b270b1def37633dd8566d776ad'}.items():assert h(a/n)==v
o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(2128,1)
s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1;r=s['rows'][0];assert r['module']=='Norm38MacroRankRaw' and 'object_sha256' not in r and not (out/'lib/DiophantineConsistency/Norm38MacroRankRaw.olean').exists()
assert r['source_sha256']=='a22def05d850d3bddb2685a45f016493ae3a10b9b931d2b137039ba9209ecfe6' and h(p/'src/DiophantineConsistency/Norm38MacroRankRaw.lean')==r['source_sha256'];assert r['deps']['exit']==0 and r['compile']['exit']==1 and r['compile']['stop_reason'] is None
for k in ('deps','compile'):assert not r[k]['monitor_errors'] and not r[k]['observed_descendant_pids'] and h(a/('Norm38MacroRankRaw-'+k+'.txt'))==r[k]['log_sha256']
log=(a/'Norm38MacroRankRaw-compile.txt').read_text();assert 'Tactic `rfl` failed' in log and 'sorryAx' in log
for n,sha in {'Norm38MacroPrefixCarrySums':'789438afddf47cad95d8657dd0d029f284fa9d3a02dc99ab33275214ffe70eb2','Norm38MacroPrefixCarryOthers':'9cc1239aeeff42841ca5d2f71796aeb859846dcefd4992fce2417e879f804279'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+n];assert dep['sha256']==sha and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':sha}
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1181
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
print(json.dumps({'status':'PASS_FAILURE_AUDIT','author_recorded_outer_session':2128,'direct_guard_slots':150,'overlay_links':1181,'scope':'failed first stage; no Lean replay'},sort_keys=True,indent=2))
