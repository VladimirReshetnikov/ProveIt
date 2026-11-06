#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-prefix-b-power-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-prefix-b-power-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
assert h(a/'state.json')=='c524139780b3cb4f1e3b66c03f8829bd1cbbd204bb6ef01ffb86f4fa962b067a' and h(a/'outer-terminal-author-record.json')=='b130a09261d68c05dfdaa35cae83ca9318c410ee896a48630e8e6a57acfa527d'
o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(80589,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1;r=s['rows'][0];n='Norm38MacroPrefixBPower';assert r['module']==n and r['object_sha256']=='e66a9ddbe1f06f6d2e593939a077494517f7351731ed41106eb23645fd26b27b' and h(out/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'] and h(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
for k in ('deps','compile'):
 x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/f'{n}-{k}.txt')==x['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log and re.search(r"'DiophantineConsistency\.Norm38MacroPrefixBPower\.d10_B_eq_b_pow' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
dep=r['dependencies']['DiophantineConsistency.Norm38MacroPrefixCarryOthers'];assert dep['sha256']=='9cc1239aeeff42841ca5d2f71796aeb859846dcefd4992fce2417e879f804279' and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':dep['sha256']}
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1181
for path,v in r['direct_guard'].items():
 q=Path(path)
 if v is None:assert not os.path.lexists(q),path
 else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
print(json.dumps({'status':'PASS','author_recorded_outer_session':80589,'direct_guard_slots':100,'overlay_links':1181,'scope':'d10 B=b^5 only; no Lean replay'},sort_keys=True,indent=2))
