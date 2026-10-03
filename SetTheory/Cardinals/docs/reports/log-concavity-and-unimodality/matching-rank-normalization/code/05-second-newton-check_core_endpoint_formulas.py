#!/usr/bin/env python3
"""Independent Boolean endpoint-state checks of all core coefficient formulas."""
from itertools import combinations_with_replacement
from math import comb
from random import Random
from pathlib import Path
import json

def count(cols):
    states={0}
    for c in cols:
        nxt=set()
        for st in states:
            avail=c&~st
            while avail:
                bit=avail&-avail;avail-=bit;nxt.add(st|bit)
        states=nxt
    return len(states)

def main():
    rng=Random(202610012);cases=checks=0
    for mask in range(512):
        core=[(mask>>(3*i))&7 for i in range(3)]
        left=[1,2,4]+[rng.randrange(1,8) for _ in range(5)]
        fullrows=core+left
        B=[sum(1<<i for i,row in enumerate(fullrows) if row>>j&1) for j in range(3)]
        LB=[sum(1<<i for i,row in enumerate(left) if row>>j&1) for j in range(3)]
        cm=[sum(1<<i for i,row in enumerate(core) if row>>j&1) for j in range(3)]
        pop={m:sum(row==m for row in fullrows) for m in range(1,8)}
        N=sum(pop.values());deg=[sum(v for m,v in pop.items() if m>>i&1) for i in range(3)]
        q=comb(N,3)-sum(comb(N-d,3) for d in deg)+sum(comb(pop[m],3) for m in (1,2,4))-sum(comb(pop[1<<i],2)*sum(v for m,v in pop.items() if m&(7^(1<<i))==7^(1<<i)) for i in range(3))
        if q!=count(B):raise RuntimeError(('total basis count',mask))
        checks+=1
        for root in range(3):
            J=cm[root];n=LB[root].bit_count();E=n+J.bit_count()
            if E!=B[root].bit_count():raise RuntimeError('root normalization')
            checks+=1
            for S in range(1,8):
                r=n*S.bit_count()+count([J,S])
                if r!=count([B[root],S]):raise RuntimeError(('exterior pair',mask,root,S))
                checks+=1
                for i in range(3):
                    if i==root:continue
                    C=cm[i];m=LB[i].bit_count();t=(LB[i]&LB[root]).bit_count();p=n*m-comb(t+1,2)
                    x=p+n*C.bit_count()+m*J.bit_count()-t*(J&C).bit_count()+count([J,C])
                    y=p*S.bit_count()+n*count([C,S])+m*count([J,S])-t*(count([J,S])+count([C,S])-count([J|C,S]))+count([J,C,S])
                    if x!=count([B[root],B[i]]) or y!=count([B[root],B[i],S]):
                        raise RuntimeError(('cross identities',mask,root,i,S))
                    checks+=2
            for S,T in combinations_with_replacement(range(1,8),2):
                value=n*count([S,T])+count([J,S,T])
                if value!=count([B[root],S,T]):raise RuntimeError(('exterior triple',mask,root,S,T))
                checks+=1
            cases+=1
    out={'labeled_cores':512,'rooted_graph_cases':cases,'exact_identity_checks':checks,'all_pass':True}
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
