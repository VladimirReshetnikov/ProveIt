#!/usr/bin/env python3
"""Physically scored exploration of equivalent PA196 axiom emitters.

Search output is not a proof. Every retained candidate must pass exact source,
startup and symbolic primitive checks, as well as logical proof transport.
"""
from pathlib import Path
import sys, json, random, time, argparse, math
from collections import Counter
from functools import lru_cache
ROOT=Path(__file__).resolve().parents[1]
SUPPORT=ROOT/'comparison_agent/selected_sources/pa_consistency_comparison_and_new196_2026-11-13/pa_consistency_research/axioms/search'
sys.path.insert(0,str(SUPPORT));sys.path.insert(0,str(ROOT/'proof_agent'))
from support import c,INC,BREAK,attrs,bad,encode,tree_word,nodes,bestcompatible_all,apply
import axiom_variants as av

TOK={'D':'node55','H':'node58','A':'node70','P':'node49','C':'node65','i':INC,
     'r':'node72','s':'node75','g':'node142','j':'node150','z':BREAK}
pair=(INC,INC);quad=(pair,pair);c.MACROS[pair]=99;c.MACROS[quad]=190
initial_machine=c.machine();c.machine=lambda:initial_machine

def legal(a,b):return a!='node142' and b!='node72'

def compress(word,rng,temp):
    xs=[TOK[x] for x in word]
    while len(xs)>1:
        co=Counter(zip(xs,xs[1:]));pairs=[]
        for p,n in co.items():
            if not legal(*p):continue
            if n>1 or p in c.MACROS:
                # Existing increment macros have no reader cost.
                bonus=1 if p in c.MACROS else 0
                pairs.append((p,n+bonus+temp*rng.expovariate(1)))
        if not pairs:break
        p=max(pairs,key=lambda x:x[1])[0];out=[];i=0
        while i<len(xs):
            if i+1<len(xs) and (xs[i],xs[i+1])==p:out.append(p);i+=2
            else:out.append(xs[i]);i+=1
        xs=out
    # Reassociate the unrepeated residue with bounded address depth. Existing
    # subtrees provide zero-cost assembly opportunities in this final parse.
    known=set()
    def collect(t):
        if c.isnode(t) and t not in known:
            known.add(t);collect(t[0]);collect(t[1])
    for t in xs:collect(t)
    @lru_cache(None)
    def dp(i,j):
        if j-i==1:return (0,xs[i],attrs(xs[i])[0])
        ans=None
        for k in range(i+1,j):
            aa=dp(i,k);bb=dp(k,j)
            if aa is None or bb is None:continue
            ca,a,ha=aa;cb,b,hb=bb
            if not legal(a,b):continue
            t=a,b;h=1+max(ha,hb)
            cost=ca+cb+(0 if t in known or t in c.MACROS else 1)
            # Small height tie-breaker avoids very deep leftover spines.
            score=cost+0.001*h
            if ans is None or score<ans[0]:ans=score,cost,t,h
        return None if ans is None else (ans[1],ans[2],ans[3])
    res=dp(0,len(xs));return None if res is None else res[1]

def score(t,exact=True):
    h,l,m,mi,_=attrs(t)
    penalty=3*bad(t)+3*max(0,m-6)+3*max(0,mi-5)+max(0,h-38)
    rows,index,shape=c.build(t);n=len(shape)
    opt=len(c.max_matching(c.opportunities_fast(rows,shape)))
    chosen=None
    if exact and n-opt+penalty<=63:
        chosen=bestcompatible_all(rows,shape);opt=len(chosen)
    return n-opt+penalty,n,opt,penalty,chosen

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--runs',type=int,default=20000);ap.add_argument('--seconds',type=int,default=600)
    ap.add_argument('--seed',type=int,default=146531);ap.add_argument('--out',type=Path,default=ROOT/'research/emitter')
    a=ap.parse_args();a.out.mkdir(parents=True,exist_ok=True);rng=random.Random(a.seed);start=time.monotonic()
    hist=Counter();best=999;bestparams=None;pool=[];evaluated=0
    def params():
        if pool and rng.random()<.85:
            p=dict(rng.choice(pool));p['permutations']=p['permutations'][:];p['order']=p['order'][:]
            move=rng.randrange(6)
            if move==0:p['bits']^=1<<rng.randrange(6)
            elif move==1:p['permutations'][rng.randrange(6)]=rng.randrange(6)
            elif move==2:
                i,j=rng.sample(range(6),2);p['order'][i],p['order'][j]=p['order'][j],p['order'][i]
            elif move==3:p['permutations'][rng.randrange(6)]=rng.randrange(6)
            elif move==4:p['gate_reverse']=not p['gate_reverse']
            return p
        return dict(bits=rng.randrange(64),order=rng.sample(range(6),6),permutations=[rng.randrange(6)for _ in range(6)],
                    h1_contrapositive=False,gate_reverse=bool(rng.randrange(2)))
    baseline=dict(bits=0,order=list(range(6)),permutations=[0]*6,h1_contrapositive=False,gate_reverse=False)
    pool=[baseline]
    for run in range(a.runs):
        if time.monotonic()-start>a.seconds:break
        p=baseline if run==0 else params();word=av.tokens(**p)
        t=compress(word,rng,rng.choice([0,.05,.2,.5,1,2]))
        if t is None:continue
        v,n,f,pen,chosen=score(t);evaluated+=1;hist[v]+=1
        if v<=best+1 and len(pool)<1000:pool.append(p)
        if v<best:
            best=v;bestparams=p
            print({'run':run,'cost':v,'nodes':n,'folds':f,'penalty':pen,'params':p,'elapsed':time.monotonic()-start},flush=True)
            (a.out/f'cost{v}.grammar.json').write_text(json.dumps(encode(t),indent=2)+'\n')
            (a.out/f'cost{v}.params.json').write_text(json.dumps(p,indent=2)+'\n')
            if v<=61 and pen==0:
                if chosen is None:chosen=bestcompatible_all(*((lambda r,i,s:(r,s))(*c.build(t))))
                rows,index,shape=c.build(t);folded,alias=apply(rows,chosen);sites,instructions,cases=c.source(t)
                validation=c.validate(folded,cases)
                print({'VALIDATION':validation},flush=True)
                (a.out/f'cost{v}.validation.json').write_text(json.dumps(validation,indent=2)+'\n')
                if validation['ok']:
                    (a.out/f'candidate{134+v}.native.tm').write_text(''.join(f'{q} {b} {w} {"R" if d else "L"} {z}\n' for(q,b),(w,d,z)in sorted(folded.items())))
                    (a.out/f'candidate{134+v}.folds.json').write_text(json.dumps(chosen,indent=2)+'\n');break
        if run and run%1000==0:print({'run':run,'best':best,'elapsed':time.monotonic()-start},flush=True)
        if run%500==499:attrs.cache_clear()
    rec={'seed':a.seed,'evaluated':evaluated,'best_effective_AX_cost':best,'best_parameters':bestparams,
         'histogram':dict(sorted(hist.items())),'elapsed_seconds':time.monotonic()-start,
         'scope':'heuristic equivalent-emitter exploration; no lower-bound claim'}
    (a.out/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(rec,flush=True)

if __name__=='__main__':main()
