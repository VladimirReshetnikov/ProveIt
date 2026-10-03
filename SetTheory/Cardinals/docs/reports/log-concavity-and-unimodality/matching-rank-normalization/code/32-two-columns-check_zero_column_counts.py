"""Direct conditioned-support check for a core column of degree zero."""
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
    rng=Random(74321);done=0;flag_cases=0
    while done<100:
        lm=[rng.randrange(1,8) for _ in range(rng.randrange(3,7))]
        rm=[rng.randrange(1,8) for _ in range(rng.randrange(3,7))]
        q=sum(matching([lm[i] for i in I]) for I in combinations(range(len(lm)),3))
        if not q or not any(matching([rm[i] for i in I]) for I in combinations(range(len(rm)),3)):continue
        ws=[rng.randrange(1,6) for _ in rm]
        n=len(lm);p=sum(matching([lm[a],lm[b]]) for a,b in combinations(range(n),2))
        e=sum(not m&1 for m in lm);d=sum(not (lm[a]|lm[b])&1 and matching([lm[a],lm[b]]) for a,b in combinations(range(n),2))
        U=sum(w*m.bit_count() for w,m in zip(ws,rm));V=sum(w*(2 if m.bit_count()==1 else 3) for w,m in zip(ws,rm));W=sum(ws)
        A=sum(ws[a]*ws[b]*sum(matching([rm[a]&mask,rm[b]&mask]) for mask in [3,5,6]) for a,b in combinations(range(len(rm)),2))
        B=sum(ws[a]*ws[b]*matching([rm[a],rm[b]]) for a,b in combinations(range(len(rm)),2))
        T=sum(prod(ws[i] for i in I)*matching([rm[i] for i in I]) for I in combinations(range(len(rm)),3))
        axis=sum(w for w,m in zip(ws,rm) if m==4)
        up=sum(w*(m&3).bit_count() for w,m in zip(ws,rm))
        vp=sum(ws[a]*ws[b]*matching([rm[a]&3,rm[b]&3]) for a,b in combinations(range(len(rm)),2))
        expected=[q+3*(p-d)+3*(n-e),q*U+(p-d)*V+(n-e)*W,q*A+(p-d)*B,q*T]
        actual=[]
        for j in range(4):
            val=0
            for J in combinations(range(len(rm)),j):
                wt=prod(ws[i] for i in J)
                for I in combinations(range(n+3),j+3):
                    masks=[]
                    for left in I:
                        if left<3:
                            core=6
                            mask=core+sum(1<<(3+i) for i,k in enumerate(J) if rm[k]>>left&1)
                        else:mask=lm[left-3]
                        masks.append(mask)
                    if matching(masks):val+=wt
            actual.append(val)
        if actual!=expected:raise RuntimeError(('subtraction mismatch',lm,rm,actual,expected))
        if 2*n*d*d>e*(2*p*p-3*n*q):raise RuntimeError('left plane Hodge')
        if 2*(p-d)**2<3*q*(n-e):raise RuntimeError('left principal Hodge')
        if 5*actual[2]**2<=12*actual[1]*actual[3]:raise RuntimeError('higher gap')
        if 8*actual[1]**2<=15*actual[0]*actual[2]:raise RuntimeError('first gap')
        coloop_free=all(any(matching([lm[j] for j in I]) for I in combinations([j for j in range(n) if j!=i],3)) for i in range(n))
        if coloop_free:
            if 8*actual[1]**2<=15*actual[0]*actual[2]:raise RuntimeError('first gap')
            flag_cases+=1
        done+=1
    return {'exact_subtraction_checks':done,'left_flag_bound_passes':True,'higher_gap_strict':True,'coloop_free_flag_cases':flag_cases,'plane_Hodge_bounds_pass':True}

if __name__=='__main__':
    result=run();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
