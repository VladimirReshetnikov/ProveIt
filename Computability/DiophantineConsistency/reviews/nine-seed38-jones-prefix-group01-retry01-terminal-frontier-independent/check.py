#!/usr/bin/env python3
import hashlib, json, os, re
from pathlib import Path
d = Path(__file__).resolve().parents[2]
p = d/'research/nine-seed38-jones-prefix-group01-retry01'
a = p/'attempt01'
out = Path('/tmp/nine-seed38-jones-prefix-group01-retry01-20261106')
def h(q): return hashlib.sha256(q.read_bytes()).hexdigest()
for name, digest in {'state.json':'f7f454ce906b932967cabf07f617aa1031200e8c7779024afd1d91ad71a8aef5','Norm38MacroPrefixGroup01-compile.txt':'5f946a8d972163f70dd018fcbb1750fe8b6e0965dc7c72e5da2815bb45824a57','outer-terminal-author-record.json':'9077a25e679930920f6d21ff37607f5185c738952b4f7fd4e0eca2b6d6b8ebc2'}.items(): assert h(a/name)==digest
outer=json.loads((a/'outer-terminal-author-record.json').read_text()); assert (outer['outer_session_id'],outer['outer_exit_code'])==(47674,0)
s=json.loads((a/'state.json').read_text()); assert s['status']=='PASS' and len(s['rows'])==1
r=s['rows'][0]; assert r['module']=='Norm38MacroPrefixGroup01'
assert r['source_sha256']=='07df9f3ac1f7fa7d6c02241385d81added00c92994060dcfb9070a99ce871cd9'
assert r['object_sha256']=='a312303ac1f6f1ce780ec12a4f74a8633a22ca6e1779feb675ef6edc8674186a'
assert h(p/'src/DiophantineConsistency/Norm38MacroPrefixGroup01.lean')==r['source_sha256']
assert h(out/'lib/DiophantineConsistency/Norm38MacroPrefixGroup01.olean')==r['object_sha256']
for k in ('deps','compile'):
 x=r[k]; assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids']
 assert h(a/('Norm38MacroPrefixGroup01-'+k+'.txt'))==x['log_sha256']
log=(a/'Norm38MacroPrefixGroup01-compile.txt').read_text()
for n in ('prefix_B','prefix_q','prefix_N'):
 assert re.search(r"'[^']*"+n+r"' depends on axioms: \[propext, Classical.choice, Quot.sound\]",log)
assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
assert set(r['dependencies'])=={'Init','DiophantineConsistency.Norm38MacroPrefixFirst'}
dep=r['dependencies']['DiophantineConsistency.Norm38MacroPrefixFirst']
assert dep['sha256']=='a69ba5536b935e388c616cc6c624ecb8da8aaef052b3350bc09d327dd8272c9a'
assert r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':dep['sha256']}
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1169
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None: assert not os.path.lexists(q),path
 else: assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path, target in s['overlay_links'].items(): assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
print(json.dumps({'status':'PASS','author_recorded_outer_session':47674,'direct_guards':100,'overlay_links':1169,'scope':'three symbolic short-prefix values; no Lean replay'},sort_keys=True,indent=2))
