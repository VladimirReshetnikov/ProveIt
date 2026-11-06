#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-dependent03-staged-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-dependent03-staged-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
assert h(a/'state.json')=='4bbe6a0229579ddd5e1861cf6d0c21d5bdb70b1d7a77e88650ce40a0219d80ee' and h(a/'outer-terminal-author-record.json')=='22c5717610cc37e6208437f0ef01b44fbfe89fffc4b8d1e2c5d463f6d01bec2c'
o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(21207,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==4
names=['Norm38MacroDependentA','Norm38MacroDependentBprime','Norm38MacroDependentW','Norm38MacroDependentC'];objects=['ae2c004e07dd9ac2c080af9845a545e7ac46fd9418996bf3f646394a82782b12','50d60722f9830d120e54a1f28d1e79c42f8aa37cec641fb39b5f8e2d29bee328','3f9a9d120dfc07e6dc0ce22145f5a9d76309838bbd7f6ae1f17f7b6efbb2b18d','8a69d181c2584313ff4add42d2197020e387b888cd676fbfa4dc465a305bd281'];reports=[['d23_M_carry','d23_U_carry','prefix_A'],['d24_R_carry','prefix_Bprime'],['d25_b_carry','d25_w_carry','prefix_W'],['d26_phi_carry','prefix_C']]
for i,(r,n,obj,ts) in enumerate(zip(s['rows'],names,objects,reports)):
 assert r['module']==n and r['object_sha256']==obj and h(out/'lib/DiophantineConsistency'/f'{n}.olean')==obj and h(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
 for k in ('deps','compile'):
  x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/f'{n}-{k}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
 for t in ts:assert re.search(r"'DiophantineConsistency\.Norm38MacroDependent03\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 mod='Norm38MacroDependentK' if i==0 else names[i-1];sha='54542c0eb712eb19b70ae07aef9308156edf7fc4311e177d00fb8181278a5f9d' if i==0 else objects[i-1];dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==sha and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':sha};assert len(r['direct_guard'])==100
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q),path
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
assert len(s['overlay_links'])==1198
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
print(json.dumps({'status':'PASS','author_recorded_outer_session':21207,'stages':4,'reports':10,'direct_guard_slots':400,'overlay_links':1198,'scope':'A/Bprime/W/C short-prefix evaluations; no Lean replay'},sort_keys=True,indent=2))
