#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-dependent07-staged-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-dependent07-staged-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
assert h(a/'state.json')=='f281330e61214079bb12fac13d3d14be64ed0a89886a00567ba33d5d95526925' and h(a/'outer-terminal-author-record.json')=='608defdec50dd01a1a6cc7a358192a862308bbb40744445472625aea0c359cfa'
o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(14608,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==5
names=['Norm38MacroDependentI','Norm38MacroDependentA0Early','Norm38MacroDependentA0','Norm38MacroDependentA1','Norm38MacroDependentV'];objects=['c12051c12de47d4971c060cd6f4e7c1da0f0962a585f5c093861274606442d72','ef424993c7b247900135b82c6cf292ab7c41ce23bdfe3d03c7f9befa635133d0','eff7a82240baac63d26df27eb612b3c1104971b0540666aa076855cd8890a9d4','ceafb76103e30efb1f9c8a9cb4c57ec2c9d294c5a6c4c6f5b85fb6f1bcc58513','93889388c58ac41b046d81d22bbdfd748ac726704bef2efe01ca6a132048d147'];reports=[['d34_Gprime_carry','prefix_I'],['d28_P_carry','d29_K_carry'],['d35_P_carry','d35_K_carry','prefix_A0'],['d36_D_carry','d36_F_carry','d36_I_carry','prefix_A1'],['d37_A0_carry','d38_A1_carry','prefix_V0','prefix_V1']]
for i,(r,n,obj,ts) in enumerate(zip(s['rows'],names,objects,reports)):
 assert r['module']==n and r['object_sha256']==obj and h(out/'lib/DiophantineConsistency'/f'{n}.olean')==obj and h(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
 for k in ('deps','compile'):
  x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/f'{n}-{k}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
 for t in ts:assert re.search(r"'DiophantineConsistency\.Norm38MacroDependent07\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 mod='Norm38MacroDependentH' if i==0 else names[i-1];sha='fd1691414fc25dab60414cdb181d1c92bcacffc621ee3fb19a6804008d4850ce' if i==0 else objects[i-1];dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==sha and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':sha};assert len(r['direct_guard'])==100
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q),path
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
assert len(s['overlay_links'])==1212
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
print(json.dumps({'status':'PASS','author_recorded_outer_session':14608,'stages':5,'reports':15,'direct_guard_slots':500,'overlay_links':1212,'scope':'I/A0/A1/V short-prefix evaluations; no Lean replay'},sort_keys=True,indent=2))
