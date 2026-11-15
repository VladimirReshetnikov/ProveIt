#!/usr/bin/env python3
"""Exact reachable failure of deleting return-scanner control34.

This rejects that drop-in scanner contract; it does not assert an absolute
halting/nonhalting theorem about the altered table.
"""
from common import *
import argparse

def step(tab,q,h,t):
    w,d,q=tab[q,int(h in t)]
    (t.add if w else t.discard)(h)
    return q,h+(1 if d else -1)

def encode(path):
    h=-2;on={h-1,h+48};on.update(h+i for i,x in enumerate(path) if int(x));pos=h+49
    for v in [0,0,0,0,0,0,2,0,0]+[1]*26:
        pos+=1;on.update(range(pos,pos+v+1));pos+=v+1
    return on

initial=encode(sites[25][0])
pq,ph,pt=74,0,set()
for tick in range(58154):pq,ph=step(rows,pq,ph,pt)
assert(pq,ph,pt)==(84,-2,initial)
short=rows.copy();short[23,0]=(0,False,75);del short[34,0];del short[34,1]
results={}
for name,tab in [('parent',rows),('shortened',short)]:
    q,h,t=84,-2,initial.copy()
    for n in range(500):
        if q==23 and h==-1 and h not in t:
            record={'steps_from_clean_frame':n,'state':q,'head':h,'ones':sorted(t)}
            trace=[]
            for duration in range(1,51):
                trace.append([q,h,int(h in t)])
                q,h=step(tab,q,h,t)
                if q==84:break
            else:raise AssertionError('No scanner return')
            record['scanner_return']={'steps':duration,'state':q,'head':h,'ones':sorted(t),'trace':trace}
            results[name]=record;break
        q,h=step(tab,q,h,t)
    else:raise AssertionError('Expected common scanner entry absent')
assert results['parent']['steps_from_clean_frame']==223
assert results['shortened']['steps_from_clean_frame']==221
assert results['parent']['ones']==results['shortened']['ones']
assert results['parent']['scanner_return']['head']==-2
assert results['shortened']['scanner_return']['head']==-1
assert results['parent']['scanner_return']['steps']==19
assert results['shortened']['scanner_return']['steps']==2
result={'status':'scanner_contract_rejected','parent_blank_start_to_frame':58154,
        'physical_primary_registers':[0,0,0,0,0,0,2,0,0],'spare_values':[1]*26,
        'source_site':25,'source_path':sites[25][0],
        'patch':'Delete native34; replace23/read0 by0 L75. All other rows unchanged.',
        'result':results,
        'scope':'The changed scanner returns one cell right of the required program-head coordinate on the actual first initialized source instruction. No global halting claim is made.'}
ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,default=HERE/'fresh_scanner_counterexample.json');a=ap.parse_args();a.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='result'},indent=2))
