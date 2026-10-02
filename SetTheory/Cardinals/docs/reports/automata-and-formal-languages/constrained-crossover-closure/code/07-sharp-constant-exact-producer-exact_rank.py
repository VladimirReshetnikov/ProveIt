"""Exact finite crossover-rank via periodic greedy-state cycle erasure."""
from collections import deque, Counter
from itertools import product
import json


def table(rows):
    a=[0]*(1<<len(rows))
    for x in range(1,len(a)):
        b=x&-x
        a[x]=a[x^b]|rows[b.bit_length()-1]
    return a


def orbit(I,F,E,rev):
    values=[]; seen={}; pair=(I,F)
    while pair not in seen:
        seen[pair]=len(values); values.append(pair)
        pair=(E[pair[0]],rev[pair[1]])
    t=seen[pair]; p=len(values)-t
    def at(i):return values[i if i<len(values) else t+(i-t)%p]
    def stable(i):return values[t+(i-t)%p]
    return t,p,at,stable


def slice_max(n,I,F,ims,at,witness=False):
    if not n:return (int(bool(I&F)),'' if I&F else None)
    layers=[at(i)[0]&at(n-i)[1] for i in range(n+1)]
    if not layers[0]:return 0,None
    dp={layers[0]:(1,'')}
    for i in range(n):
        nd={}
        for a in (0,1):
            restart=ims[a][layers[i]]&layers[i+1]
            if not restart:continue
            for z,(rank,w) in dp.items():
                nz=ims[a][z]&layers[i+1]
                nr=rank
                if not nz:nz=restart;nr+=1
                if nr>nd.get(nz,(-1,''))[0]:nd[nz]=(nr,w+str(a) if witness else '')
        dp=nd
    rank,w=max(dp.values())
    return rank,w if witness else None


def exact_rank(n,rows0,rows1,I,F,witness=False):
    size=1<<n
    ims=[table(rows0),table(rows1)]
    Erows=[x|y for x,y in zip(rows0,rows1)]
    E=table(Erows)
    rev=table([sum(1<<u for u in range(n) if Erows[u]>>v&1) for v in range(n)])
    t,p,at,stable=orbit(I,F,E,rev)
    for r in range(p):
        if not stable(r)[0]&F:continue
        S=[stable(a)[0]&stable(r-a)[1] for a in range(p)]
        a0=t%p
        todo=[(a0,S[a0])]; seen=set(todo)
        for a,z in todo:
            aa=(a+1)%p
            for c in (0,1):
                if not ims[c][S[a]]&S[aa]:continue
                zz=ims[c][z]&S[aa]
                if not zz:return {'finite':False,'t':t,'p':p}
                q=(aa,zz)
                if q not in seen:seen.add(q);todo.append(q)
    H=max(1,2*t+p*(size-1)-1)
    best=(int(bool(I&F)),0,'' if I&F else None)
    for length in range(1,H+1):
        rank,w=slice_max(length,I,F,ims,at,witness)
        if rank>best[0]:best=(rank,length,w)
    return {'finite':True,'rank':best[0],'length':best[1],'witness':best[2], 't':t,'p':p,'horizon':H}


def census(n):
    size=1<<n; matrices=list(product(range(size),repeat=n))
    counts=Counter();examples={};total=0
    for a,b in product(matrices,repeat=2):
        for I,F in product(range(1,size),repeat=2):
            z=exact_rank(n,a,b,I,F)
            key=str(z['rank']) if z['finite'] else 'infinite'
            counts[key]+=1;total+=1
            if key not in examples:
                zz=exact_rank(n,a,b,I,F,True)
                examples[key]={'zero':a,'one':b,'I':I,'F':F,**zz}
    return {'n':n,'total':total,'counts':dict(sorted(counts.items())), 'examples':examples}

if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('--states',type=int,default=2);args=ap.parse_args()
    result=census(args.states)
    print(json.dumps(result,indent=2))
