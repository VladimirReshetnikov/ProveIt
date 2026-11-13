#!/usr/bin/env python3
"""Point-in-time binding of all eight directly referenced producer rows."""
import hashlib,json,os
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1];BASE=Path('/tmp/nine-sharing-sign32-substitution-group07-check-20261106');H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(v,msg):
 if not v:raise RuntimeError(msg)
records=json.loads((P/'providers.json').read_text())['rows'];need(len(records)==8,'producer count')
for i,rec in enumerate(records):
 need(rec['index']==i,'producer order');name=f'Sign32Substitution{i:02d}';packet=D/f'research/nine-sharing-sign32-substitution-group{i:02d}-check/attempt01';base=Path(f'/tmp/nine-sharing-sign32-substitution-group{i:02d}-check-20261106')
 need(H(packet/'state.json')==rec['state_sha256'] and H(packet/'outer-result.json')==rec['outer_sha256'],'receipt '+name)
 d=json.loads((packet/'state.json').read_text());o=json.loads((packet/'outer-result.json').read_text());need(d['status']=='PASS' and len(d['rows'])==1 and o['author_observed_numeric_outer_exit']==0,'status '+name);r=d['rows'][0]
 need(r['module']==name and r['source_sha256']==rec['source_sha256'] and r['object_sha256']==rec['object_sha256'] and r['deps']['exit']==0 and r['compile']['exit']==0,'row '+name)
 obj=base/'lib/DiophantineConsistency'/f'{name}.olean';need(H(base/'src/DiophantineConsistency'/f'{name}.lean')==rec['source_sha256'] and H(obj)==rec['object_sha256'],'source/object '+name)
 for k in ('deps','compile'):need(H(base/f'{name}-{k}.txt')==rec[k+'_log_sha256'] and r[k]['log_sha256']==rec[k+'_log_sha256'],'log '+name)
 for path,v in r['direct_guard'].items():
  q=Path(path)
  if v is None:need(not os.path.lexists(q),'unexpected '+path)
  else:need(q.is_file() and str(q.resolve())==v['realpath'] and H(q)==v['sha256'],'guard '+path)
 route=BASE/'lib/DiophantineConsistency'/f'{name}.olean';need(route.is_file() and route.resolve()==obj.resolve() and H(route)==rec['object_sha256'],'overlay route '+name)
print(json.dumps({'status':'PASS','producer_rows':8,'scope':'point-in-time source/object/log/guards/routes; transitive ancestry inherited'},sort_keys=True))
