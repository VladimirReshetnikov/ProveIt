#!/usr/bin/env python3
"""Equivalent-head search retaining/reassociating an existing AX layout."""
from emitter_search import *
from support import repl,rotations

def expand(t):
    raw=c.raw_nodes()
    def go(x):
        if isinstance(x,str) and x.startswith('x'):return go(raw[x])
        if c.isnode(x):return tuple(go(y) for y in x)
        return x
    return go(t)

def paint(t,word):
    it=iter(word)
    def go(x):
        if c.isnode(x):return go(x[0]),go(x[1])
        return TOK[next(it)]
    ans=go(t)
    if next(it,None) is not None:raise ValueError('word length differs')
    return ans

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=int,default=600);ap.add_argument('--seed',type=int,default=145681);ap.add_argument('--out',type=Path,default=ROOT/'research/reskin')
    a=ap.parse_args();a.out.mkdir(parents=True,exist_ok=True);rng=random.Random(a.seed);start=time.monotonic()
    base=expand('x67');word0=av.BASE
    baseline=dict(bits=0,order=list(range(6)),permutations=[0]*6,h1_contrapositive=False,gate_reverse=False)
    assert tree_word(base)==tuple(TOK[x]for x in word0)
    hist=Counter();best=62;pool=[(base,baseline)];p=baseline;t=base;v=62;trials=0
    for cycle in range(10000):
        if time.monotonic()-start>a.seconds:break
        t,p=rng.choice(pool);v=score(t)[0]
        for j in range(800):
            if time.monotonic()-start>a.seconds:break
            nt=t;np=dict(p);np['permutations']=p['permutations'][:];np['order']=p['order'][:]
            move=rng.randrange(10)
            if move<5:
                ch=sorted(nodes(t),key=repr);x=rng.choice(ch);opts=list(rotations(x))
                if not opts:continue
                nt=repl(t,x,rng.choice(opts))
            else:
                if move<7:np['permutations'][rng.randrange(6)]=rng.randrange(6)
                elif move==7:np['bits']^=1<<rng.randrange(6)
                elif move==8:
                    i,k=rng.sample(range(6),2);np['order'][i],np['order'][k]=np['order'][k],np['order'][i]
                else:np['gate_reverse']=not np['gate_reverse']
                nw=av.tokens(**np)
                if len(nw)!=len(av.tokens(**p)):continue
                nt=paint(t,nw)
            nv,n,f,pen,chosen=score(nt);trials+=1;hist[nv]+=1
            temp=.08+.55*(1-j/800)
            if nv<=v or rng.random()<math.exp((v-nv)/temp):t,p,v=nt,np,nv
            if nv<best:
                best=nv;print({'cycle':cycle,'j':j,'cost':nv,'nodes':n,'folds':f,'penalty':pen,'params':np,'elapsed':time.monotonic()-start},flush=True)
                (a.out/f'cost{nv}.grammar.json').write_text(json.dumps(encode(nt),indent=2)+'\n')
                (a.out/f'cost{nv}.params.json').write_text(json.dumps(np,indent=2)+'\n')
                if nv<=61 and pen==0:
                    rows,index,shape=c.build(nt);chosen=bestcompatible_all(rows,shape);folded,aliases=apply(rows,chosen)
                    ss,ins,cs=c.source(nt);val=c.validate(folded,cs);print({'VALIDATION':val},flush=True)
                    (a.out/f'cost{nv}.validation.json').write_text(json.dumps(val,indent=2)+'\n')
                    if val['ok']:
                        (a.out/f'candidate{134+nv}.native.tm').write_text(''.join(f'{q} {b} {w} {"R" if d else "L"} {z}\n'for(q,b),(w,d,z)in sorted(folded.items())))
                        (a.out/f'candidate{134+nv}.folds.json').write_text(json.dumps(chosen,indent=2)+'\n')
                        result={'found':True,'states':134+nv,'trials':trials,'params':np};print(result);(a.out/'receipt.json').write_text(json.dumps(result,indent=2)+'\n');return
            if nv<=62 and len(pool)<200 and rng.random()<.05:pool.append((nt,np))
            if trials%2000==0:attrs.cache_clear()
        print({'cycle':cycle,'trials':trials,'best':best,'current':v,'pool':len(pool),'seconds':time.monotonic()-start},flush=True)
    rec={'found':False,'seed':a.seed,'trials':trials,'best':best,'histogram':dict(sorted(hist.items())),'elapsed_seconds':time.monotonic()-start}
    (a.out/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(rec,flush=True)

if __name__=='__main__':main()
