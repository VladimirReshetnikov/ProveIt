#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-prefix-rank-composition-retry01';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-prefix-rank-composition-retry01-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
assert h(a/'state.json')=='e7ee28c3c956544568e0b7e0b51fc8db89e768b98875a1a54c84e3f3ef040a0a' and h(a/'outer-terminal-author-record.json')=='ec7489da37acfec2503ec6498b2ab2ee4978ca21ad9b8ebfebf84ad09d75a35e'
o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(1460,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];n='Norm38MacroRankComposition';assert r['module']==n and r['object_sha256']=='682aefdc3bde128ef02c981a75c84230ade20e306cfadefd3f49f99fe7bcb548' and h(out/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'] and h(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/f'{n}-{k}.txt')==x['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log and re.search(r"'DiophantineConsistency\.Norm38MacroRankComposition\.d11_rankCode' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
for mod,sha in {'Norm38MacroRankCodeLink':'5a200be6ed07ad99ee680339c8a6383f4140f586fb1dcb311ad4e7eea1557259','Norm38MacroPrefixBPower':'e66a9ddbe1f06f6d2e593939a077494517f7351731ed41106eb23645fd26b27b'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==sha and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':sha}
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1185
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
print(json.dumps({'status':'PASS','author_recorded_outer_session':1460,'direct_guard_slots':150,'overlay_links':1185,'scope':'d11 short-prefix rankCode composition; no Lean replay'},sort_keys=True,indent=2))
