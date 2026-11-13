#!/usr/bin/env python3
import hashlib,json,os,re
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-dependent06-staged-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-dependent06-staged-check-20261106')
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
assert h(a/'state.json')=='ebac1154ca7b2edf83ef00603fb172f99c75acd8f9c06b047897354210fe9cd8' and h(a/'outer-terminal-author-record.json')=='16911b6ece9d52c32acd5890d22bd199bf2e771d33a557aa1e085f1343c2ab05'
o=json.loads((a/'outer-terminal-author-record.json').read_text());assert (o['session_id'],o['exit_code'])==(17939,0)
s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==4
names=['Norm38MacroDependentJcarry','Norm38MacroDependentGprime','Norm38MacroDependentHcarry','Norm38MacroDependentH'];objects=['0809e12f38ec0f941c442e21bbf2b29da09ad72674ae0306fdb3e2b555802750','c2f085832ccfda5cead9ac08d342594c98ee4dcb0d24e2f40def0b92cbd784aa','42d9186ed5f52558b2faa2a18c981e7fef66de04a7b914be2588ad0554e2ffad','fd1691414fc25dab60414cdb181d1c92bcacffc621ee3fb19a6804008d4850ce'];reports=[['d25_j_carry'],['d32_A_carry','d32_C_carry','d32_D_carry','prefix_Gprime'],['d33_j_carry','d33_Bprime_carry'],['d33_C_carry','prefix_H']]
for i,(r,n,obj,ts) in enumerate(zip(s['rows'],names,objects,reports)):
 assert r['module']==n and r['object_sha256']==obj and h(out/'lib/DiophantineConsistency'/f'{n}.olean')==obj and h(p/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256']
 for k in ('deps','compile'):
  x=r[k];assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'];assert h(a/f'{n}-{k}.txt')==x['log_sha256']
 log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
 for t in ts:assert re.search(r"'DiophantineConsistency\.Norm38MacroDependent06\."+t+r"' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
 mod='Norm38MacroDependentF' if i==0 else names[i-1];sha='a7700d99911c457d906075eccae9433ac825b8b9fc0df269c01bfd66426b2118' if i==0 else objects[i-1];dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==sha and r['direct_guard'][dep['path']]=={'realpath':dep['realpath'],'sha256':sha};assert len(r['direct_guard'])==100
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:assert not os.path.lexists(q),path
  else:assert q.is_file() and str(q.resolve())==v['realpath'] and h(q)==v['sha256'],path
assert len(s['overlay_links'])==1208
for path,target in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==target,path
print(json.dumps({'status':'PASS','author_recorded_outer_session':17939,'stages':4,'reports':9,'direct_guard_slots':400,'overlay_links':1208,'scope':'Gprime/H short-prefix evaluations; no Lean replay'},sort_keys=True,indent=2))
