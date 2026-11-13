#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-prefix-group05-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-prefix-group05-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
assert h(a/'state.json')=='5fbdc90a27715d92d22606b2aaeea39cfac8338657631cc9f21d94c7c425c72a' and h(a/'outer-terminal-author-record.json')=='6bca954a651f6e8042fedeb4c08885294efbec256c85440169963caa3d143ad2'
o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(45791,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];n='Norm38MacroPrefixQNCarry';assert r['module']==n and r['object_sha256']=='bd2995f482e56f212b821cb5ced4a9f660119720e20a57cb71aeedf9294c194c' and h(out/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'] and h(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/f'{n}-{k}.txt')==x['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for t in ('d10_q','d10_N'):assert re.search(r"'DiophantineConsistency\.Norm38MacroPrefixGroup05\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
dep=r['dependencies']['DiophantineConsistency.Norm38MacroPrefixGlarge'];assert dep['sha256']=='b685399878adfa8efc0fae22b6f9793c1f74079b4266cfff15d86a6a25e89a06' and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':dep['sha256']}
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1178
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
print(json.dumps({'status':'PASS','author_recorded_outer_session':45791,'reports':2,'direct_guard_slots':100,'overlay_links':1178,'scope':'q/N short-prefix values; no Lean replay'},sort_keys=True,indent=2))
