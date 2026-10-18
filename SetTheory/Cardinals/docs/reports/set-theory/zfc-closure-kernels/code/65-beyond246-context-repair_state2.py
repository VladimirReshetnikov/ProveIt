#!/usr/bin/env python3
"""Try deleting state2 while synthesizing its sole difficult incoming action."""
from collections import Counter
import itertools,json,time
import fold_search as f


def main():
    T={k:(w,d,4 if t==2 else t) for k,(w,d,t) in f.OLD.items() if k[0]!=2}
    oracle,macros=f.derive(T)
    rows=set()
    for proof in macros['proofs']+list(f.m.BLOCK_PROOFS.values()):
        for step in proof['trace']:
            if 'state' in step:rows.add((step['state'],step['read']))
    assert (20,0) not in rows
    for k in rows:assert k in T
    f.AFFINE.oracle=oracle
    table={(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in T.items()}
    counts=Counter();found=[];began=time.monotonic()
    for i,(w,d,target) in enumerate(itertools.product((0,1),('L','R'),[q for q in f.STATES if q!=2])):
        table['20',0]=(w,d,str(target))
        try:
            result=f.v.check_sites(f.AFFINE,table,f.SITES)
            candidate=T.copy();candidate[20,0]=(w,d,target)
            label=f'{w}{d}{target}'
            (f.ROOT/('state2-repair-'+label+'.tm')).write_text(f.encode(candidate,f.START))
            (f.ROOT/('state2-repair-'+label+'.json')).write_text(json.dumps(dict(instructions=result,macros=macros),indent=2)+'\n')
            found.append((w,d,target));counts['PASS']+=1
            print('SUCCESS',w,d,target,flush=True)
        except Exception as exc:
            counts[type(exc).__name__+':'+str(exc)[:100]]+=1
        if (i+1)%100==0:print('done',i+1,'seconds',time.monotonic()-began,'found',found,flush=True)
    summary=dict(cases=i+1,found=found,seconds=time.monotonic()-began,reused_macro_rows=sorted(rows),counts=dict(counts))
    (f.ROOT/'state2-repair-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
