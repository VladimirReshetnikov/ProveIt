#!/usr/bin/env python3
"""Bind narrow seed syntax and current data imports to prior guarded observations."""
import hashlib,json,os
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];BASE=Path('/tmp/nine-sharing-sign15-staged-syntax-check-20261110');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,m):
 if not v:raise RuntimeError(m)
checks=[('research/nine-sharing-sign15-staged-syntax-check/attempt01/state.json','1206640f983ea92ff4605976dce480ed7fd52189400d2441b69db5553ee80412','/tmp/nine-sharing-sign15-staged-syntax-check-20261110',14,'SharingSeed15Degree124'),('research/nine-sharing-norm38-current-ports-split-draft/attempt01/state.json','0f89b8b0a53abd15b0d7c1e20f198495775628e104fabc247c24efbd2cb81ad4','/tmp/nine-sharing-norm38-current-ports-split-20261105',0,'Norm38CurrentPortBase')]
result={}
for state,pin,root,i,name in checks:
 state=D/state;root=Path(root);need(H(state)==pin,'state pin');d=json.loads(state.read_text());r=d['rows'][i];need(r['module']==name and r['deps']['exit']==0 and r['compile']['exit']==0,'successful row '+name)
 if name=='SharingSeed15Degree124':need(d['status']=='PASS','sign15 producer status')
 else:need(d['status']=='FAILED','port producer overall scope')
 obj=root/'lib/DiophantineConsistency'/f'{name}.olean';need(H(root/'src/DiophantineConsistency'/f'{name}.lean')==r['source_sha256'] and H(obj)==r['object_sha256'],'source/object '+name)
 for k in ('deps','compile'):need(H(root/f'{name}-{k}.txt')==r[k]['log_sha256'],'log '+name)
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:need(not os.path.lexists(q),'unexpected '+path)
  else:need(q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256'],'guard '+path)
 if name=='SharingSeed15Degree124':rec={'sha256':r['object_sha256'],'realpath':str(obj.resolve())};target=name
 else:
  target='CurrentKernelData2011';obs=r['dependencies']['DiophantineConsistency.'+target];g=r['direct_guard'].get(obs['path']);need(g is not None and g['sha256']==obs['sha256'] and g['realpath']==obs['realpath'],'data observation');rec={'sha256':obs['sha256'],'realpath':obs['realpath']}
 q=BASE/'lib/DiophantineConsistency'/f'{target}.olean';need(q.is_file() and str(q.resolve())==rec['realpath'] and H(q)==rec['sha256'],'base route '+target);result[target]=rec
print(json.dumps({'status':'PASS','observed':result,'scope':'sign20 syntax producer plus current-data direct observation from successful row of failed producer; deeper ancestry inherited'},sort_keys=True))
