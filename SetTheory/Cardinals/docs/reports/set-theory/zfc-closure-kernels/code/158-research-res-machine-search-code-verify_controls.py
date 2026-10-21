#!/usr/bin/env python3
"""Exhaustively compare the C++ synthetic survivors with independent checkers.

The checked universe has 24 possible actions per row, hence 576 complete
two-row assignments for each control. No K218 conclusion follows from the
controls alone.
"""
from pathlib import Path
import hashlib,itertools,json,time
import check_joint_fold as equal
import check_shifted as shifted

ROOT=Path(__file__).resolve().parent.parent

def rows_key(rows):return tuple(tuple(row)for row in rows)

def verify(directory=ROOT/'controls'):
    began=time.monotonic();results=[]
    for name,old_file,delta in [('equal','two-row-control.tm',0),('shifted','shifted-control-1.tm',-2)]:
        old,start=equal.read(directory/old_file);keep,drop=1,2
        states=sorted({q for q,b in old}-{drop});phi=lambda q:keep if q==drop else q
        actions=list(itertools.product((0,1),(-1,1),states+[254]))
        domain=equal.domain(old,start,3);passing=[];rejected=0
        for a0,a1 in itertools.product(actions,repeat=2):
            new={(q,b):(w,d+(delta if z==drop else 0),phi(z))
                 for(q,b),(w,d,z)in old.items()if q!=drop}
            new[keep,0]=a0;new[keep,1]=a1
            try:
                if delta:shifted.check(old,new,start,start,keep,drop,delta,3,97)
                else:equal.check(old,new,start,start,keep,drop,3,97,domain)
            except ValueError:rejected+=1
            else:passing.append(rows_key((a0,a1)))
        specs=sorted(directory.glob(f'controls-{name}-*.tm.json'))
        discovered=[rows_key(json.loads(p.read_text())['rows'])for p in specs]
        if len(discovered)!=len(set(discovered)) or sorted(passing)!=sorted(discovered):
            raise ValueError(f'C++/independent-checker survivor disagreement for {name}')
        result=json.loads((directory/f'controls-{name}-result.json').read_text())
        if result['covered_rejections']!=rejected or result['hits']!=len(passing):
            raise ValueError('C++ counts disagree with independent exhaustive enumeration')
        results.append(dict(family=name,complete_assignments=len(actions)**2,
                            rejected=rejected,survivors=len(passing),
                            exact_survivor_sets_agree=True))
    return dict(status='EXHAUSTIVE_SYNTHETIC_CONTROL_AGREEMENT',results=results,
                equal_checker_sha256=hashlib.sha256(Path(equal.__file__).read_bytes()).hexdigest(),
                shifted_checker_sha256=hashlib.sha256(Path(shifted.__file__).read_bytes()).hexdigest(),
                seconds=time.monotonic()-began,
                scope='Every two-action assignment on two six-state synthetic controls; separate repository diagram checkers. This validates the C++ implementation on these finite examples, not on all machines.')

if __name__=='__main__':
    result=verify();out=ROOT/'controls/exhaustive-agreement.json'
    out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
