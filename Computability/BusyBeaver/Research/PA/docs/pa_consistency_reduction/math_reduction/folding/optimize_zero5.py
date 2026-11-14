#!/usr/bin/env python3
"""Find <=196-state AX grammar avoiding every run of six zero path bits."""
from pathlib import Path
import sys,random,math,time,functools,re,json
import optimize_closed as O
MACRO_PATHS={a:[p for p,op in O.S.flatten(t)]for a,t in O.ATOM_RAW.items()}
MACRO_PATHS['B']=[()]
@functools.lru_cache(maxsize=100000)
def bad(t,z=0):
    if isinstance(t,str):
        return sum(any(len(v)>5 for v in re.findall('0+','0'*z+''.join(map(str,p)))) for p in MACRO_PATHS[t])
    return bad(t[0],z+1)+bad(t[1],0)
def main():
    budget=int(sys.argv[1])if len(sys.argv)>1 else 200000
    seed=int(sys.argv[2])if len(sys.argv)>2 else 627122
    rng=random.Random(seed);start=time.monotonic();base=O.START
    t=base;bestt=base;phys=O.evaluate(base)[0];score=best=50*phys+bad(base)
    ties=[base];nties=1;seen={base}
    print('BASE',phys,'bad',bad(base),'shape',O.zero_shape(base),flush=True)
    for it in range(budget):
        if it%3000==0:t=rng.choice([base,bestt]+ties);score=50*O.evaluate(t)[0]+bad(t)
        cand=t
        for _ in range(2 if rng.random()<.16 else 1):
            p,q=rng.choice(O.paths(cand));a,b=q
            if rng.randrange(2):
                if not isinstance(a,tuple):continue
                u,v=a;alt=u,(v,b)
            else:
                if not isinstance(b,tuple):continue
                u,v=b;alt=(a,u),v
            cand=O.replace(cand,q,alt)if rng.random()<.72 else O.replace_one(cand,p,alt)
        if it%10000==0:print('progress',it,'best',best/50,'current',score/50,'seconds',round(time.monotonic()-start,1),flush=True)
        if cand in seen:continue
        seen.add(cand)
        p,n,c,ds=O.evaluate(cand)
        if p>=1000:continue
        nb=bad(cand);s=50*p+nb;temp=50*(.5*(1-(it%3000)/3000)+.05)
        if s<=score or rng.random()<math.exp((score-s)/temp):t=cand;score=s
        if s<=best:
            if s<best:
                best=s;bestt=cand;ties=[];nties=0
                print('BEST',s/50,'states',p,'bad',nb,it,flush=True)
            nties+=1
            if len(ties)<150:ties.append(cand)
            elif rng.randrange(nties)<150:ties[rng.randrange(150)]=cand
        if p<=196 and nb==0:
            path=Path(__file__).with_name(f'zero5_{p}_{seed}_{it}.json');O.output(cand,path)
            print('TARGET',path.name,O.evaluate(cand),flush=True)
            result=O.validate(cand,path);print('VALIDATE',result,flush=True)
            if not result['failures']:break
    O.output(bestt,Path(__file__).with_name(f'zero5_best_{seed}.json'))
    for i,t in enumerate(ties[:20]):O.output(t,Path(__file__).with_name(f'zero5_tie_{seed}_{i}.json'))
    print('DONE',best/50,'states',O.evaluate(bestt)[0],'bad',bad(bestt),'visited',len(seen),'seconds',round(time.monotonic()-start,1),flush=True)
if __name__=='__main__':main()
