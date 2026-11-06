#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-prefix-group06-staged-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-prefix-group06-staged-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
assert h(a/'state.json')=='a3c660f1b2c892bc9aae2a46c15ba1ce73012b91df1871581ac0334db9dc1054' and h(a/'outer-terminal-author-record.json')=='0e43ba6357f107ebadc1fb5df1c96c02aba3d2fa0b34bbf66851245024ce3539'
o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(18979,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==2
names=['Norm38MacroPrefixCarrySums','Norm38MacroPrefixCarryOthers'];objects=['789438afddf47cad95d8657dd0d029f284fa9d3a02dc99ab33275214ffe70eb2','9cc1239aeeff42841ca5d2f71796aeb859846dcefd4992fce2417e879f804279'];reports=[['d10_e_carry','d10_ell_carry','d10_lambda_carry'],['d10_g_carry','d10_theta_carry','d10_B_carry','d10_b_carry']]
for r,n,obj,rs in zip(s['rows'],names,objects,reports):
 assert r['module']==n and r['object_sha256']==obj and h(out/'lib/DiophantineConsistency'/f'{n}.olean')==obj and h(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
 for k in ('deps','compile'):
  x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/f'{n}-{k}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
 for t in rs:assert re.search(r"'DiophantineConsistency\.Norm38MacroPrefixGroup06\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 dep=r['dependencies']['DiophantineConsistency.Norm38MacroPrefixQNCarry'];assert dep['sha256']=='bd2995f482e56f212b821cb5ced4a9f660119720e20a57cb71aeedf9294c194c' and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':dep['sha256']}
 assert len(r['direct_guard'])==100
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q),path
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
assert len(s['overlay_links'])==1179
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
print(json.dumps({'status':'PASS','author_recorded_outer_session':18979,'stages':2,'reports':7,'direct_guard_slots':200,'overlay_links':1179,'scope':'d10 short-prefix carry values; no Lean replay'},sort_keys=True,indent=2))
