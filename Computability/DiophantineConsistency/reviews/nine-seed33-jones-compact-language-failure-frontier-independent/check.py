#!/usr/bin/env python3
import hashlib,json,os
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-seed33-jones-compact-language-check';A=P/'attempt01';O=Path('/tmp/nine-seed33-jones-compact-language-check-20261106');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(A/'state.json')=='7cd3124ef2828b60aabcc368435dded8893ef8e3795d8f8b74b79c50733f008c' and sha(A/'outer-terminal-author-record.json')=='286ef3e83d0b3e934d2483646167c3a637e0a27c8470a90ef5c19b8342bde4d7';o=json.loads((A/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(55561,1)
s=json.loads((A/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1 and len(s['overlay_links'])==1268 and s['runner_sha256']==sha(P/'run.py')=='89b7b671bc89d8b2d9453ed39075c8dd463bfc64b90a24b793567157531c5873';r=s['rows'][0];n='Sign33MacroLanguage';assert r['module']==n and r['source_sha256']=='de51ea7d49bbf72cb046f50b8000027bf723a59e4d54ae17368ee7490da7e864'==sha(P/'src/DiophantineConsistency'/f'{n}.lean')==sha(O/'src/DiophantineConsistency'/f'{n}.lean') and len(r['direct_guard'])==100 and 'object_sha256' not in r
for phase,code in [('deps',0),('compile',-6)]:
 v=r[phase];assert v['exit']==code and v['stop_reason'] is None and not v['monitor_errors'] and not v['observed_descendant_pids'];assert sha(A/f'{n}-{phase}.txt')==sha(O/f'{n}-{phase}.txt')==v['log_sha256']
assert r['compile']['peak_session_rss_bytes']==2939863040
v=r['dependencies']['DiophantineConsistency.Sign33NamedFormula'];assert v['sha256']=='ba39e705f4cc32ec52ddf0fc992d1500139f46b270bbe36cba07bddcbac1435f' and r['direct_guard'][v['path']]=={'sha256':v['sha256'],'realpath':v['realpath']}
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q)
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and sha(q)==v['sha256']
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target
log=(A/f'{n}-compile.txt').read_text();assert sha(A/f'{n}-compile.txt')=='48bc2200174632932b9ea98fd0a0c30e6dc353ce535531045f1c7efc7b79940a' and 'lean::memory_exception' in log and "at 'interpreter'" in log and 'depends on axioms' not in log
print(json.dumps({'status':'PASS_FAILURE_AUDIT','author_session':55561,'lean_exit':-6,'sampled_peak_bytes':2939863040,'monitor_stop':None,'scope':'language module failed; no object or final postflight; author-recorded outer outcome'},indent=2,sort_keys=True))
