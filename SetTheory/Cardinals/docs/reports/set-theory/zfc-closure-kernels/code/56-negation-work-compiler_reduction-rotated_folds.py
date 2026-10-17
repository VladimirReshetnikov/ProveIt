#!/usr/bin/env python3
"""Uniform and mixed-row folds after one neutral source reassociation."""
from collections import defaultdict,Counter
import json,time
from pathlib import Path
import search_structural as s

HERE=Path(__file__).resolve().parent/'rotated252'
data=json.loads((HERE/'source.json').read_text())
nodes={int(q):tuple(map(tuple,v)) for q,v in data['nodes'].items()};root=data['root']
table=s.audit.read_table((HERE/'machine.tm').read_bytes());states={q for q,b in table}
cases=list(s.cases(nodes,root));usage=defaultdict(set)
current=None
class Tracking(dict):
    def __getitem__(self,k):usage[int(k[0]),k[1]].add(current);return super().__getitem__(k)
strings=Tracking({(str(q),b):(w,d,str(t)) for(q,b),(w,d,t) in table.items()})
def check(table,index):
    p,e,z,physical,target=cases[index]
    try:
        s.strict.run(table,p,(physical,z) if e[0]=='D' else None,target,halt=e[0]=='H',fuel=1000)
        return True,None
    except (AssertionError,KeyError) as ex:return False,str(ex)
begin=time.monotonic()
for current in range(len(cases)):
    ok,why=check(strings,current);assert ok,(current,why)
current=None
print('BASELINE runtime8391; changed labels128,255; original12 retired',flush=True)
protected=s.PROTECTED|{96}
results=[];survivors=[]
for dead in (128,255,110):
    assert dead not in protected
    for target in sorted(states-{dead}):
        for mask in (0,1,2,3):
            if mask and target in protected:continue
            candidate={}
            for (q,b),row in table.items():
                if q==dead:continue
                if q==target and mask&(1<<b):row=table[dead,b]
                w,d,t=row;candidate[q,b]=w,d,target if t==dead else t
            if any(candidate[k]!=table[k] for k in s.audit.BOX_PAIRS):continue
            ss={(str(q),b):(w,d,str(t)) for(q,b),(w,d,t) in candidate.items()}
            witnesses=set(usage[dead,0])|set(usage[dead,1])
            for b in (0,1):
                if mask&(1<<b):witnesses.update(usage[target,b])
            fail=None
            for index in sorted(witnesses,key=lambda i:len(cases[i][0])):
                ok,why=check(ss,index)
                if not ok:fail=index,why;break
            record=dict(deleted=dead,target=target,mask=mask)
            if fail:record.update(outcome='runtime_failure',failure=fail)
            else:
                for index in range(len(cases)):
                    ok,why=check(ss,index)
                    if not ok:fail=index,why;break
                if fail:record.update(outcome='full_runtime_failure',failure=fail)
                else:
                    startup,_=s.boot(candidate,1000000);record.update(outcome='runtime_survivor',boot=startup)
                    (HERE/f'candidate_{dead}_{target}_{mask}.tm').write_bytes(s.audit.encode(candidate))
                    survivors.append(record.copy());print('SURVIVOR',record,flush=True)
            results.append(record)
    print('DELETED',dead,'recipes',len(results),'survivors',len(survivors),'seconds',round(time.monotonic()-begin,1),flush=True)
    (HERE/'fold-results.json').write_text(json.dumps(dict(scope='Full original register program after closed source reassociation; exact 4-box conditional affine checks; finite boot only for survivors; no kernel proof.',recipes=len(results),survivors=survivors,elapsed_seconds=time.monotonic()-begin,results=results),indent=2)+'\n')
