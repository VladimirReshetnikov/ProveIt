"""Bounded one-row repairs after shortening the frozen delimiter counter.

The strict affine checker remains conditional on its four register-box contracts.
This diagnostic alters no box-support row; it is not a semantic impossibility proof.
"""
import common as c
from pathlib import Path
from collections import Counter
import json, time

began=time.monotonic()
base=c.fold(c.T,'74','84')
counter=(9,13,19,29,41,58,84)
states=sorted({q for q,b in base}, key=int)
cases=[57]+[i for i in range(len(c.CASES)) if i!=57]
result={'baseline':c.check(c.T),'deleted':74,'redirected_to':84,'edited_sources':list(counter),'recipes':0,'failures':Counter(),'survivors':[],'best':[]}
for q in counter:
    for b in (0,1):
        for w in (0,1):
            for d in ('L','R'):
                for t in states:
                    key=str(q),b
                    row=w,d,t
                    if row==base[key]:continue
                    candidate=base.copy();candidate[key]=row
                    check=c.check(candidate,cases)
                    result['recipes']+=1
                    if check['passed']:
                        result['survivors'].append({'row':[q,b,w,d,int(t)],'check':check})
                    else:
                        result['failures'][check['case']]+=1
                        if check['preceding_passes']>0:
                            result['best'].append({'row':[q,b,w,d,int(t)],'check':check})
    print(q,result['recipes'],len(result['survivors']),len(result['best']),time.monotonic()-began,flush=True)
result['seconds']=time.monotonic()-began
result['failures']=dict(result['failures'])
(Path(__file__).parent/'delimiter_repair_results.json').write_text(json.dumps(result,indent=2)+'\n')
print('RESULT',result['recipes'],len(result['survivors']),len(result['best']),result['seconds'])
