"""Independent endpoint enumeration for the matching-hole cubic identity."""
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
    rng=Random(72019);counts=[0]*4;hard=0
    for holes in range(4):
        while counts[holes]<40:
            lm=[rng.randrange(1,8) for _ in range(rng.randrange(3,7))]
            rm=[rng.randrange(1,8) for _ in range(rng.randrange(3,7))]
            if not any(matching([lm[i] for i in I]) for I in combinations(range(len(lm)),3)):continue
            if not any(matching([rm[i] for i in I]) for I in combinations(range(len(rm)),3)):continue
            weights=[rng.randrange(1,8) for _ in rm]
            n=len(lm);p=sum(matching([lm[i] for i in I]) for I in combinations(range(n),2));q=sum(matching([lm[i] for i in I]) for I in combinations(range(n),3))
            ds=[sum(matching([lm[a],lm[b]]) for a,b in combinations(range(n),2) if not (lm[a]|lm[b])>>i&1) if i<holes else 0 for i in range(3)]
            W=sum(weights);U=sum(m.bit_count()*v for m,v in zip(rm,weights));V=sum((2 if m.bit_count()==1 else 3)*v for m,v in zip(rm,weights))
            B=sum(prod(weights[i] for i in I)*matching([rm[i] for i in I]) for I in combinations(range(len(rm)),2))
            A=sum(prod(weights[i] for i in I)*sum(matching([rm[i]&mask for i in I]) for mask in [3,5,6]) for I in combinations(range(len(rm)),2))
            T=sum(prod(weights[i] for i in I)*matching([rm[i] for i in I]) for I in combinations(range(len(rm)),3))
            us=[sum(w*m.bit_count() for w,m in zip(weights,rm) if not m>>i&1) for i in range(3)]
            vs=[sum(weights[a]*weights[b] for a,b in combinations(range(len(rm)),2) if not (rm[a]|rm[b])>>i&1 and matching([rm[a],rm[b]])) for i in range(3)]
            expected=[q+3*p+3*n+1-sum(ds),q*U+p*V+n*W-sum(d*u for d,u in zip(ds,us)),q*A+p*B-sum(d*v for d,v in zip(ds,vs)),q*T]
            actual=[]
            for j in range(4):
                val=0
                for J in combinations(range(len(rm)),j):
                    wt=prod(weights[i] for i in J)
                    for I in combinations(range(n+3),j+3):
                        masks=[]
                        for left in I:
                            if left<3:
                                core=7^(1<<left) if left<holes else 7
                                mask=core+sum(1<<(3+i) for i,k in enumerate(J) if rm[k]>>left&1)
                            else:mask=lm[left-3]
                            masks.append(mask)
                        if matching(masks):val+=wt
                actual.append(val)
            if actual!=expected:raise RuntimeError(('conditional count failed',holes,lm,rm,actual,expected))
            hard_case=all(sum(bool(m>>i&1) for m in lm)>=2 for i in range(3))
            if hard_case:
                g=[n-3,p-2*n+3,q-n+2,3*q-p,p-sum(ds),*ds,*[q-2*d for d in ds],*[p-d-2*n+4 for d in ds],2*p*p-3*n*q,n*(n-1)-2*p,2*p*p*(n-2)-3*n*(n-1)*q,n*(n-1)*(n-2)-6*q]
                if min(g)<0:raise RuntimeError(('flag constraint failed',g,lm))
                if 8*actual[1]**2<=15*actual[0]*actual[2] or 5*actual[2]**2<=12*actual[1]*actual[3]:raise RuntimeError('strict gap failed')
                hard+=1
            counts[holes]+=1
    return {'direct_conditional_graphs':sum(counts),'by_number_of_holes':counts,'hard_flag_cases':hard,'all_identities_and_constraints_passed':True}

if __name__=='__main__':
    result=run();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
