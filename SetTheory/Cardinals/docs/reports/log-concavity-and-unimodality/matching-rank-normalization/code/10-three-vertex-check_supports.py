#!/usr/bin/env python3
"""Independent finite endpoint-set regressions; not substitutes for the proof."""
from itertools import combinations
from functools import lru_cache
from pathlib import Path
import json
import random

@lru_cache(None)
def states(cols):
    out={0}
    for c in cols:
        nxt=set()
        for s in out:
            avail=c&~s
            while avail:
                bit=avail&-avail;avail-=bit;nxt.add(s|bit)
        out=nxt
    return out

def supports(cols, us, vs):
    coeff=[0]*(min(len(cols),len(us))+1)
    for k in range(len(coeff)):
        for J in combinations(range(len(cols)),k):
            wy=1
            for j in J:wy*=vs[j]
            for I in states(tuple(cols[j] for j in J)):
                wx=1
                for i,u in enumerate(us):
                    if I>>i&1:wx*=u
                coeff[k]+=wy*wx
    while len(coeff)>1 and not coeff[-1]:coeff.pop()
    return coeff

def product(p,q):
    out=[0]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q):out[i+j]+=a*b
    return out

def main():
    rng=random.Random(20261001)
    marginal=0
    for trial in range(240):
        cols=[rng.randrange(1,8) for _ in range(rng.randrange(1,9))]
        vs=[rng.randrange(1,10) for _ in cols]
        c={0:1}
        for k in range(1,4):
            for I in range(1,8):
                if I.bit_count()!=k:continue
                value=0
                for J in combinations(range(len(cols)),k):
                    if I in states(tuple(cols[j] for j in J)):
                        w=1
                        for j in J:w*=vs[j]
                        value+=w
                c[I]=value
        for i,j in combinations(range(3),2):
            ci,cj=c[1<<i],c[1<<j]
            common=[v for m,v in zip(cols,vs) if m>>i&1 and m>>j&1]
            overlap=sum(common)**2+sum(v*v for v in common)
            if 2*c[(1<<i)|(1<<j)]!=2*ci*cj-overlap:
                raise RuntimeError('Overlap identity failed')
        for i in range(3):
            j,k=[a for a in range(3) if a!=i]
            if c[(1<<i)|(1<<j)]*c[(1<<i)|(1<<k)]<c[1<<i]*c[7]:
                raise RuntimeError('Rayleigh specialization failed')
        marginal+=1
    star=0;genuine=0
    for trial in range(160):
        q=1+trial%4;n=rng.randrange(0,5);m=rng.randrange(1,7)
        # All core edges are incident to A0.
        core=rng.randrange(1,1<<q)
        L=[rng.randrange(1,1<<q) for _ in range(n)]
        R=[rng.randrange(1,8) for _ in range(m)]
        Bcols=[((core>>j)&1)|sum(((row>>j)&1)<<(3+i) for i,row in enumerate(L)) for j in range(q)]
        cols=Bcols+R
        us=[rng.randrange(1,7) for _ in range(3+n)]
        vs=[rng.randrange(1,7) for _ in cols]
        full=supports(cols,us,vs)
        u0=us[0]
        # Sector decomposition is counted independently with the root activity zero.
        left1=[us[0]]+us[3:]
        cols1=[((c&1)|((c>>3)<<1)) for c in Bcols]
        p1=supports(cols1,left1,vs[:q]);p2=supports(R,us[:3],vs[q:])
        zero1=supports(cols1,[0]+left1[1:],vs[:q])
        zero2=supports(R,[0]+us[1:3],vs[q:])
        size=max(len(p1),len(zero1));p1+= [0]*(size-len(p1));zero1+=[0]*(size-len(zero1))
        size=max(len(p2),len(zero2));p2+= [0]*(size-len(p2));zero2+=[0]*(size-len(zero2))
        use1=[a-b for a,b in zip(p1,zero1)];use2=[a-b for a,b in zip(p2,zero2)]
        rhs=product(zero1,zero2)
        for part in [product(use1,zero2),product(zero1,use2)]:
            rhs += [0]*max(0,len(part)-len(rhs))
            for k,v in enumerate(part):rhs[k]+=v
        while len(rhs)>1 and rhs[-1]==0:rhs.pop()
        if rhs!=full:raise RuntimeError('Rooted gluing identity failed')
        D=q+3
        full += [0]*(D+1-len(full))
        for k in range(1,D):
            if k*(D-k)*full[k]**2 < (k+1)*(D-k+1)*full[k-1]*full[k+1]:
                raise RuntimeError('Fixed-cover ULC failed')
        star+=1;genuine+=bool(full[D])
    out={'marginal_graphs':marginal,'weighted_star_graphs':star,'genuine_covers':genuine,'all_pass':True}
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
