"""Direct conditioned-support check for a core row having no B neighbors."""
from itertools import combinations
from math import prod
from random import Random
from pathlib import Path
import json

def matching(masks):
    states={0}
    for mask in masks:
        states={used|1<<i for used in states for i in range(6) if mask>>i&1 and not used>>i&1}
    return bool(states)

def run():
    rng=Random(74321);done=0
    while done<100:
        lm=[rng.randrange(1,8) for _ in range(rng.randrange(3,7))]
        rm=[rng.randrange(1,8) for _ in range(rng.randrange(3,7))]
        q=sum(matching([lm[i] for i in I]) for I in combinations(range(len(lm)),3))
        if not q or not any(matching([rm[i] for i in I]) for I in combinations(range(len(rm)),3)):continue
        ws=[rng.randrange(1,6) for _ in rm]
        n=len(lm);p=sum(matching([lm[a],lm[b]]) for a,b in combinations(range(n),2))
        projected=sum(matching([lm[a]&3,lm[b]&3]) for a,b in combinations(range(n),2));d=p-projected;e=lm.count(4)
        U=sum(w*m.bit_count() for w,m in zip(ws,rm));V=sum(w*(2 if m.bit_count()==1 else 3) for w,m in zip(ws,rm));W=sum(ws)
        A=sum(ws[a]*ws[b]*sum(matching([rm[a]&mask,rm[b]&mask]) for mask in [3,5,6]) for a,b in combinations(range(len(rm)),2))
        B=sum(ws[a]*ws[b]*matching([rm[a],rm[b]]) for a,b in combinations(range(len(rm)),2))
        T=sum(prod(ws[i] for i in I)*matching([rm[i] for i in I]) for I in combinations(range(len(rm)),3))
        W0=sum(w for w,m in zip(ws,rm) if not m&1);u=sum(w*m.bit_count() for w,m in zip(ws,rm) if not m&1)
        v=sum(ws[a]*ws[b] for a,b in combinations(range(len(rm)),2) if not (rm[a]|rm[b])&1 and matching([rm[a],rm[b]]))
        expected=[q+2*p+n,q*U+p*(V-u)+n*(W-W0),q*A+p*(B-v),q*T]
        actual=[]
        for j in range(4):
            val=0
            for J in combinations(range(len(rm)),j):
                wt=prod(ws[i] for i in J)
                for I in combinations(range(n+3),j+3):
                    masks=[]
                    for left in I:
                        if left<3:
                            core=0 if left==0 else 7
                            mask=core+sum(1<<(3+i) for i,k in enumerate(J) if rm[k]>>left&1)
                        else:mask=lm[left-3]
                        masks.append(mask)
                    if matching(masks):val+=wt
            actual.append(val)
        if actual!=expected:raise RuntimeError(('subtraction mismatch',lm,rm,actual,expected))
        if 2*d*d-4*e*q>2*p*p-3*n*q:raise RuntimeError('left flag inequality')
        if 5*actual[2]**2<=12*actual[1]*actual[3]:raise RuntimeError('higher gap')
        if 8*actual[1]**2<=15*actual[0]*actual[2]:raise RuntimeError('first gap')
        done+=1
    return {'exact_subtraction_checks':done,'left_flag_bound_passes':True,'both_gaps_strict':True}

if __name__=='__main__':
    result=run();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
