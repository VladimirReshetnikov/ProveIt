#!/usr/bin/env python3
"""Finish the proposed-oracle screen for surviving relocated box entries."""
import json
from collections import Counter
from pathlib import Path
import time
import mixed_box_search as m

root=m.ROOT
r=json.loads((root/'experiments/mixed_box_results.json').read_text())
strict,_=m.load_strict();cc,_=m.cases(strict);oracle=strict.oracle
table=m.base.read_table((root/'sources/candidate-permutation252/zfc_permutation252_old.tm').read_bytes())
ordinary={(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in table.items()}
usage=[]
for pc,branch,target,halt in cc:
    tracked=m.Track(ordinary);_,n=strict.run(tracked,pc,branch,target,halt=halt,fuel=1000)
    assert n>0;usage.append(tracked.used)
out=[];start=time.monotonic()
for record in r['affine_results']:
    if record['status']!='macro_entry_relocation_requires_new_contract':continue
    dead,keep,bit=record['recipe']
    def relocated(q,branch,state):
        ans=oracle(str(dead),branch,state) if q==str(keep) else None
        if ans is None:ans=oracle(q,branch,state)
        if ans is None:return None
        stop,effect=ans
        return (str(keep) if stop==str(dead) else stop),effect
    strict.oracle=relocated
    current={k:(w,d,str(keep) if t==str(dead) else t) for k,(w,d,t) in ordinary.items() if k[0]!=str(dead)}
    w,d,t=ordinary[str(dead),bit];current[str(keep),bit]=(w,d,str(keep) if t==str(dead) else t)
    affected={(str(keep),bit)}|{k for k,v in ordinary.items() if k[0]==str(dead) or v[2]==str(dead)}
    order=sorted(range(len(cc)),key=lambda i:not bool(usage[i]&affected))
    passed=0
    for i in order:
        pc,branch,target,halt=cc[i]
        try:
            rules,n=strict.run(current,pc,branch,target,halt=halt,fuel=1000)
            assert n>0;passed+=1
        except (AssertionError,KeyError) as ex:
            out.append(dict(recipe=[dead,keep,bit],status='checker_rejection',passed=passed,case=i,error=str(ex)));break
    else:
        out.append(dict(recipe=[dead,keep,bit],status='conditional_pass',passed=passed))
        print('CONDITIONAL SURVIVOR',dead,keep,bit,flush=True)
strict.oracle=oracle
result=dict(scope='Proposed renamed entries and exits; finite box tests do not supply universal contracts.',results=out,elapsed_seconds=time.monotonic()-start)
(root/'experiments/relocated_entry_results.json').write_text(json.dumps(result,indent=2)+'\n')
print('screened',len(out),'status',dict(Counter(x['status'] for x in out)),flush=True)
