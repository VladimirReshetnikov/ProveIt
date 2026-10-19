#!/usr/bin/env python3
"""List every failed full guarded instruction contract for one scanner edit."""
from pathlib import Path
import sys,json,time
from collections import Counter
import os
BASE=Path(os.environ.get('ZFC245_REFERENCE', str(Path(__file__).resolve().parent.parent/'packages/zfc245-proof-20261018'))).resolve()
sys.path.insert(0,str(BASE/'code'))
sys.path.insert(0,str(BASE/'reference/context246/code'))
import parametric_prefix_affine as affine
from review_affine_source import full_inc,full_strip
table={}
for line in (BASE/'certificate/machine_old.tm').read_text().splitlines():
    if line and not line.startswith('#'):
        q,b,w,d,t=line.split();table[q,int(b)]=(int(w),d,t)
del table['58',0];del table['58',1];table['41',0]=(0,'L','84')
affine.PADDING=64
sites=json.loads((BASE/'certificate/sites_physical.json').read_text())
cases,failures=0,[]
for index,(p,op,r) in enumerate(sites):
    for zero in ((True,False) if op=='CD' else (None,)):
        branch=(r,zero) if op=='CD' else None
        extra,effect,overflow=0,None,False
        if op=='CI': successor,overflow=full_inc(p);effect=('inc',r)
        elif op=='CD' and not zero: successor,overflow=full_inc(p);effect=('dec',r);extra=1
        elif op=='CD': successor,overflow=full_inc(full_strip(p,'0',1))
        elif op=='CB': successor,overflow=full_inc(full_strip(p,'0',r))
        elif op=='CC': successor=full_strip(p,'1',r)
        else: successor=''
        right=[('b',int(b)) for b in successor]+[('r',0,1,64+extra+int(overflow)-len(successor)),('b',1),('box',('plain',effect))]
        try:
            affine.run(table,p,branch,affine.canon([('b',1)],right),halt=(op=='CH'),fuel=1000)
        except Exception as e:
            failures.append({'index':index,'path':p,'opcode':op,'register':r,'zero':zero,'error':repr(e)})
        cases+=1
result={'cases':cases,'failures':failures,'failed_cases':len(failures),'by_opcode':dict(Counter(x['opcode'] for x in failures))}
path=Path(__file__).parent/'shorter58-full-failures.json';path.write_text(json.dumps(result,indent=2)+'\n')
print({k:v for k,v in result.items() if k!='failures'})
