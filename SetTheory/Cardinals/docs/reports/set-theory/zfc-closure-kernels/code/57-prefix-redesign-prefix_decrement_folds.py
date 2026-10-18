#!/usr/bin/env python3
"""Screen single-state reuse in the prefix-right decrement prototype.

All positive decrement source sites are checked against exact concrete tapes.
This is a finite rejection census, not an unbounded correctness proof.
"""
from collections import Counter
import json,time
import prefix_decrement as p

def mutate(table,dead,keep,mode):
    changed={k:(w,d,keep if t==dead else t) for k,(w,d,t) in table.items() if k[0]!=dead}
    if mode>=0:
        w,d,t=table[dead,mode];changed[keep,mode]=w,d,keep if t==dead else t
    return changed

def main():
    begun=time.monotonic();table=p.generate();cases=list(p.cases())
    # Every physical register with contrasting primary values appears before
    # the complete all-site suite, improving only rejection speed.
    first={}
    for i,case in enumerate(cases):first.setdefault((case[1],i%9),i)
    initial=list(first.values());initialset=set(initial)
    order=initial+[i for i in range(len(cases)) if i not in initialset]
    for i in initial:
        result,_=p.run(table,cases[i]);assert result['passed'],(i,result)
    states=sorted({q for q,b in table});recipes=[]
    for dead in (85,97,112,131):
        for keep in states:
            if keep in (dead,96):continue
            for mode in (-1,0,1):
                if mode>=0 and table[dead,mode]==table[keep,mode]:continue
                recipes.append((dead,keep,mode))
    result=dict(scope=__doc__,baseline_cases=len(cases),recipes=len(recipes),
                failures=[],survivors=[],literal_checks=0)
    for n,(dead,keep,mode) in enumerate(recipes):
        changed=mutate(table,dead,keep,mode)
        for i in order:
            check,_=p.run(changed,cases[i]);result['literal_checks']+=1
            if not check['passed']:
                result['failures'].append([dead,keep,mode,i,check['reason']]);break
        else:
            print('SURVIVOR',dead,keep,mode,flush=True)
            result['survivors'].append([dead,keep,mode])
            (p.HERE/f'prefix-decrement-fold-{dead}-{keep}-{mode}.tm').write_bytes(p.m.audit.encode(changed))
        if (n+1)%500==0:print('Checked',n+1,'seconds',round(time.monotonic()-begun,3),flush=True)
    result['failure_reasons']=dict(Counter(x[4] for x in result['failures']))
    result['total_seconds']=time.monotonic()-begun
    (p.HERE/'prefix_decrement_folds.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('failures','scope')},indent=2))

if __name__=='__main__':main()
