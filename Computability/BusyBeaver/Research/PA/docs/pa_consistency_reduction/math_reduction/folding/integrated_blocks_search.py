#!/usr/bin/env python3
"""Jointly anneal eight logically equivalent integrated-gate words and grammars."""
from pathlib import Path
import sys,json,random,time,math
import integrated_flexible as F
G=F.G;O=F.O
VARIANTS=json.loads(Path(__file__).with_name('integrated_variants.json').read_text())
FULL=[];START=[]
def relabel(t,word):
    it=iter(word)
    def go(q):return next(it)if isinstance(q,str)else(go(q[0]),go(q[1]))
    val=go(t)
    try:next(it);assert False,'unconsumed tokens'
    except StopIteration:pass
    return val
for v in VARIANTS:
    opaque=relabel(G.initial,v['word']);t=G.opened(opaque);START.append(t);FULL.append(O.expand(t))
assert len({len(x)for x in FULL})==1

def expanded_word(word):
    return sum((O.expand(G.opened(c))for c in word),[])
HEADLEN=len(expanded_word(G.PREFIX+sum((h for i,h in enumerate(G.HEADS)if i!=4),[])))
EQLEN=len(expanded_word(G.code(G.eq)));MEMLEN=len(expanded_word(G.code(G.mem)))
SEPLEN=len(expanded_word(G.code(G.sep)));POINTLEN=len(expanded_word(G.code(G.point)))
XLEN=len(expanded_word(G.code(G.x)))
def swap(t,lo,a,b):
    left=G.sub(t,lo,lo+a);right=G.sub(t,lo+a,lo+a+b)
    return G.patch(t,lo,lo+a+b,(right,left))
def change(t,v,bit):
    if bit==1:
        a,b=(MEMLEN,EQLEN)if v&2 else(EQLEN,MEMLEN)
        return swap(t,HEADLEN,a,b)
    if bit==0:
        a,b=(POINTLEN,SEPLEN)if v&1 else(SEPLEN,POINTLEN)
        return swap(t,HEADLEN+EQLEN+MEMLEN,a,b)
    lo=HEADLEN+EQLEN+MEMLEN+SEPLEN+POINTLEN
    sub=G.sub(t,lo,lo+XLEN)
    return G.patch(t,lo,lo+XLEN,relabel(sub,FULL[v^4][lo:lo+XLEN]))
START=[]
for i in range(8):
    t=G.START;v=0
    for bit in range(3):
        if i&(1<<bit):t=change(t,v,bit);v^=1<<bit
    assert O.expand(t)==FULL[i],i
    START.append(t)

def output(t,v,path):
    assert O.expand(t)==FULL[v]
    O.output(t,path);d=json.loads(path.read_text());d.update(design='integrated equality witness gate',variant=VARIANTS[v],generated_stack_heads=7,dropped_stack_heads=[5],opaque_word=VARIANTS[v]['word']);path.write_text(json.dumps(d,indent=2))

def main():
    budget=int(sys.argv[1])if len(sys.argv)>1 else 200000
    seed=int(sys.argv[2])if len(sys.argv)>2 else 104937
    rng=random.Random(seed);start=time.monotonic();vals=[O.evaluate(t)[0]for t in START]
    v=min(range(8),key=vals.__getitem__);t=START[v];best=score=vals[v];bestt=(t,v);ties=[(s,j)for j,s in enumerate(START)if vals[j]==best];nties=len(ties)
    print('INITIAL',vals,'best',best,'fulltokens',len(FULL[0]),flush=True)
    seen={hash(t)}
    for it in range(budget):
        if it%4000==0:t,v=rng.choice([bestt]+ties);score=O.evaluate(t)[0]
        vi=v
        if rng.random()<.06:
            bit=rng.randrange(3);vi=v^(1<<bit);cand=change(t,v,bit)
        else:
            cand=t
            for _ in range(2 if rng.random()<.14 else 1):
                p,q=rng.choice(O.paths(cand));a,b=q
                if rng.randrange(2):
                    if not isinstance(a,tuple):continue
                    u,w=a;alt=u,(w,b)
                else:
                    if not isinstance(b,tuple):continue
                    u,w=b;alt=(a,u),w
                cand=O.replace(cand,q,alt)if rng.random()<.72 else O.replace_one(cand,p,alt)
        if it%10000==0:print('progress',it,'best',best,'current',score,'variant',v,'seconds',round(time.monotonic()-start,1),flush=True)
        hh=hash(cand)
        if hh in seen:continue
        seen.add(hh);s,n,c,ds=O.evaluate(cand);temp=.6*(1-(it%4000)/4000)+.06
        if s<1000 and(s<=score or rng.random()<math.exp((score-s)/temp)):t=cand;v=vi;score=s
        if s<=best:
            if s<best:
                best=s;bestt=(cand,vi);ties=[];nties=0
                p=Path(__file__).with_name(f'integrated_blocks_best_{seed}.json');output(cand,vi,p)
                print('BEST',s,n,c,vi,it,flush=True)
            nties+=1
            if len(ties)<150:ties.append((cand,vi))
            elif rng.randrange(nties)<150:ties[rng.randrange(150)]=(cand,vi)
            if s<196:
                p=Path(__file__).with_name(f'integrated_blocks_{s}_{seed}_{it}.json');output(cand,vi,p);result=F.check(cand,p);print('TARGET',result,flush=True)
                if not result['failures']:break
    output(bestt[0],bestt[1],Path(__file__).with_name(f'integrated_blocks_best_{seed}.json'))
    print('DONE',best,len(seen),'seconds',round(time.monotonic()-start,1),flush=True)
if __name__=='__main__':main()
