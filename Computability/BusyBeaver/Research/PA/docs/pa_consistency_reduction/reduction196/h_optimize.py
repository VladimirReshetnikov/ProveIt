from pathlib import Path
import sys,json,random,math,time
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'verification'))
import optimize_open_safe as O
import symbolic as S
variant=S.load_machine(ROOT/'comparison/audit/h_catalan_node170_3_133_37.tm')
O.BASE={k:v for k,v in variant.items()if k[0]<134}

def main(budget=300000,seed=190221):
    rng=random.Random(seed);base=O.opened(O.tree('x67'));bestt=base;best=O.evaluate(base)[0]
    t=base;score=best;start=time.monotonic();ties=[];seen={base}
    print('BASE',O.evaluate(base),flush=True)
    for it in range(budget):
        if it%3000==0:t=rng.choice([base,bestt]+ties[-12:]);score=O.evaluate(t)[0]
        cand=t
        for _ in range(2 if rng.random()<.14 else 1):
            ps=O.paths(cand);p,q=rng.choice(ps);a,b=q
            if rng.randrange(2):
                if not isinstance(a,tuple):continue
                u,v=a;alt=(u,(v,b))
            else:
                if not isinstance(b,tuple):continue
                u,v=b;alt=((a,u),v)
            cand=O.replace(cand,q,alt)if rng.random()<.7 else O.replace_one(cand,p,alt)
        if cand in seen:continue
        seen.add(cand)
        if len(O.nodes(cand))>83:continue
        s,n,c,ds=O.evaluate(cand)
        temp=.48*(1-(it%3000)/3000)+.07
        if s<1000 and(s<=score or rng.random()<math.exp((score-s)/temp)):t=cand;score=s
        if s<=best:
            if s<best:best=s;bestt=cand;print('BEST',best,n,c,it,round(time.monotonic()-start,1),flush=True)
            if len(ties)<300:ties.append(cand)
            if s<196:
                path=Path(__file__).with_name(f'h_open_safe_{s}_{it}.json');O.output(cand,path)
                print('TARGET',str(path),ds,flush=True)
                break
        if it%20000==0:print('progress',it,best,score,round(time.monotonic()-start,1),flush=True)
    print('DONE',best,len(seen),round(time.monotonic()-start,1),flush=True)

if __name__=='__main__':main(int(sys.argv[1])if len(sys.argv)>1 else 300000,int(sys.argv[2])if len(sys.argv)>2 else 190221)
