"""Direct conditioned-support check for a core column adjacent only to A3."""
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

from replay_all import setup

def evaluate(poly,vals):
    return sum(c*prod(x**k for x,k in zip(vals,mon)) for mon,c in poly.a.items())

def run():
    rng=Random(74321);done=0;flag_cases=0
    while done<100:
        lm=[rng.randrange(1,8) for _ in range(rng.randrange(3,7))]
        rm=[rng.randrange(1,8) for _ in range(rng.randrange(3,7))]
        q=sum(matching([lm[i] for i in I]) for I in combinations(range(len(lm)),3))
        if not q or not any(matching([rm[i] for i in I]) for I in combinations(range(len(rm)),3)):continue
        ws=[rng.randrange(1,6) for _ in rm]
        n=len(lm);p=sum(matching([lm[a],lm[b]]) for a,b in combinations(range(n),2))
        f1=sum(not m&2 for m in lm);f2=sum(not m&4 for m in lm)
        g1=sum(not (lm[a]|lm[b])&2 and matching([lm[a],lm[b]]) for a,b in combinations(range(n),2))
        g2=sum(not (lm[a]|lm[b])&4 and matching([lm[a],lm[b]]) for a,b in combinations(range(n),2))
        U=sum(w*m.bit_count() for w,m in zip(ws,rm));V=sum(w*(2 if m.bit_count()==1 else 3) for w,m in zip(ws,rm));W=sum(ws)
        A=sum(ws[a]*ws[b]*sum(matching([rm[a]&mask,rm[b]&mask]) for mask in [3,5,6]) for a,b in combinations(range(len(rm)),2))
        B=sum(ws[a]*ws[b]*matching([rm[a],rm[b]]) for a,b in combinations(range(len(rm)),2))
        T=sum(prod(ws[i] for i in I)*matching([rm[i] for i in I]) for I in combinations(range(len(rm)),3))
        V3=sum(w*sum(matching([6&mask,r&mask]) for mask in [3,5,6]) for w,r in zip(ws,rm))
        V1=sum(w*sum(matching([1&mask,r&mask]) for mask in [3,5,6]) for w,r in zip(ws,rm))
        B3=sum(ws[a]*ws[b]*matching([6,rm[a],rm[b]]) for a,b in combinations(range(len(rm)),2))
        B1=sum(ws[a]*ws[b]*matching([1,rm[a],rm[b]]) for a,b in combinations(range(len(rm)),2))
        W6=sum(w for w,r in zip(ws,rm) if r&6);W4=sum(w for w,r in zip(ws,rm) if r&4)
        singles=(n-f2)*W+f2*W6
        expected=[q+3*p-g1-2*g2+3*n-f2+1,q*U+(p-g1-g2)*V+g1*V3+g2*V1+singles,q*A+(p-g1-g2)*B+g1*B3+g2*B1,q*T]
        actual=[]
        for j in range(4):
            val=0
            for J in combinations(range(len(rm)),j):
                wt=prod(ws[i] for i in J)
                for I in combinations(range(n+3),j+3):
                    masks=[]
                    for left in I:
                        if left<3:
                            core=[5,3,3][left]
                            mask=core+sum(1<<(3+i) for i,k in enumerate(J) if rm[k]>>left&1)
                        else:mask=lm[left-3]
                        masks.append(mask)
                    if matching(masks):val+=wt
            actual.append(val)
        if actual!=expected:raise RuntimeError(('subtraction mismatch',lm,rm,actual,expected))
        if 5*actual[2]**2<=12*actual[1]*actual[3]:raise RuntimeError('higher gap')
        bounds=[2*(p*p-g1*g1-g2*g2)-3*q*n,2*(p-g2)**2-3*q*(n-f2)]
        if min(bounds)<0:raise RuntimeError(('flag bounds',lm,bounds))
        if 20*actual[2]**2-48*actual[1]*actual[3]<9*q*T*singles:raise RuntimeError('quantitative higher gap')
        coloop_free=all(any(matching([lm[j] for j in I]) for I in combinations([j for j in range(n) if j!=i],3)) for i in range(n))
        if coloop_free:
            gs=setup('transpose')[1]
            values=[evaluate(poly,[n,p,q,g1,g2,f1,f2]) for poly in gs]
            if min(values)<0:raise RuntimeError(('generator',lm,values))
            if 8*actual[1]**2<=15*actual[0]*actual[2]:raise RuntimeError('first gap')
            flag_cases+=1
        done+=1
    return {'exact_transpose_star_edge_support_checks':done,'higher_gap_bound_pass':True,'coloop_free_cases':flag_cases,'all_generators_pass':True}

if __name__=='__main__':
    result=run();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
