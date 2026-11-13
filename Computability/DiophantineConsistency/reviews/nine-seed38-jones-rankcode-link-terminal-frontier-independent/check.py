#!/usr/bin/env python3
import hashlib,json,os
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-rankcode-link-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-rankcode-link-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
assert h(a/'state.json')=='6a91660e068615b3b53c5c90f9badd8124c4ef75bb9163e79e2dd0907460314a' and h(a/'outer-terminal-author-record.json')=='b449308e49b7c78e41a706cfaa62006a3aa05ecbf08700341bd09474242b0ee0'
o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(43451,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];n='Norm38MacroRankCodeLink';assert r['module']==n and r['object_sha256']=='5a200be6ed07ad99ee680339c8a6383f4140f586fb1dcb311ad4e7eea1557259' and h(out/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'] and h(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/f'{n}-{k}.txt')==x['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log and "'DiophantineConsistency.Norm38MacroRankCodeLink.rankRaw_eq_rankCode' depends on axioms: [propext]" in log
dep=r['dependencies']['DiophantineConsistency.Norm38MacroRankCarry'];assert dep['sha256']=='60217f4104203c8fde8da56182d932e5382b9b7b118962b8f0a392dd799e6c89' and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':dep['sha256']}
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1183
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
print(json.dumps({'status':'PASS','author_recorded_outer_session':43451,'direct_guard_slots':100,'overlay_links':1183,'axioms':['propext'],'scope':'generic rank identity only; no Lean replay'},sort_keys=True,indent=2))
