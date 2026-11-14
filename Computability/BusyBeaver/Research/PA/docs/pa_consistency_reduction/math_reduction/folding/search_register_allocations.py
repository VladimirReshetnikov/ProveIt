#!/usr/bin/env python3
"""All8! register allocations fixing initial N, scored by compatible folds."""
from pathlib import Path
import sys,itertools,time,json,collections
import compatible_folds as F
S=F.S;C=F.C

def main():
    original,tree,allocated,entry=C.compile_grammar(None)
    oldphysical=S.PHYSICAL.copy();protected={q for q,b in S.ENGINE_ROWS}|{original[k][2]for k in S.ENGINE_ROWS if k in original}|{0,S.ROOT}
    endpoints={q for q,b in original if q not in protected}
    entries={r:q for q,r in S.SKIPS.items()}
    calls=[(k,w,d,S.SKIPS[z])for k,(w,d,z)in original.items()if k not in S.ENGINE_ROWS and z in S.SKIPS]
    indices=[i for i in range(9)if i!=6]
    best=999;out=[];start=time.monotonic();counter=collections.Counter()
    for it,ys in enumerate(itertools.permutations(indices)):
        perm=list(range(9))
        for a,b in zip(indices,ys):perm[a]=b
        m=original.copy()
        for k,w,d,r in calls:m[k]=(w,d,entries[perm[r]])
        opts=F.candidates(m,endpoints);sel,tested=F.best_subset(m,opts)
        score=len(m)//2-len(sel);counter[score]+=1
        if score<best:
            best=score;item=dict(permutation=perm,physical=[perm[r]for r in oldphysical],states=score,folds=sel,options=len(opts));out.append(item)
            print('BEST',json.dumps(item),'it',it,'seconds',round(time.monotonic()-start,1),flush=True)
        if score<196:
            mm,mu=F.fold(m,sel);S.PHYSICAL=[perm[r]for r in oldphysical]
            result=C.check(mm,tree,True);S.PHYSICAL=oldphysical
            path=Path(__file__).with_name(f'allocated_{score}_{it}.json')
            path.write_text(json.dumps(dict(permutation=perm,physical=[perm[r]for r in oldphysical],folds=sel,check=result),indent=2))
            path.with_suffix('.tm').write_text(''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(mm.items())))
            print('VALIDATE',result,'file',path.name,flush=True)
            if not result['failures']:break
        if it%2000==0:print('progress',it,'best',best,'seconds',round(time.monotonic()-start,1),flush=True)
    report=dict(best=best,histogram=dict(counter),best_records=out,seconds=time.monotonic()-start)
    Path(__file__).with_name('register_allocations.json').write_text(json.dumps(report,indent=2));print('DONE',report,flush=True)
if __name__=='__main__':main()
