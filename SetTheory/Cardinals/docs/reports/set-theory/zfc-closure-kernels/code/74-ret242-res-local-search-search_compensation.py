from search_folds import *
from functools import lru_cache
import time

def search(k=4,limit=14):
    seen=reachable_windows(k)
    oldtrails={}
    pats={}
    for q in Q:
        for b in (0,1):
            pats[q,b]=[p for p in seen[q] if (p>>k)&1==b]
            oldtrails[q,b]={p:set(trail(q,p,k,limit)) for p in pats[q,b]}
    incoming=defaultdict(list)
    for edge,(_,_,q) in T.items():incoming[q].append(edge)
    solutions=[];start=time.time()
    allpairs=len(sys.argv)>2 and sys.argv[2]=='all'
    pairs=[(q,r,which) for q in Q for r in Q if q!=r and q!=95 and (allpairs or any(T[q,b]==T[r,b] for b in (0,1))) for which in ((1,2,3) if allpairs else (3,))]
    for qi,(q,r,which) in enumerate(pairs):
        if qi%10000==0:print('pair',qi,'elapsed',round(time.time()-start,2),flush=True)
        newT={edge:(w,d,r if target==q else target) for edge,(w,d,target) in T.items() if edge[0]!=q}
        for b in (0,1):
            if which&(1<<b):
                w,d,target=T[q,b];newT[r,b]=(w,d,r if target==q else target)
        checks=[edge for edge in set(incoming[q]+incoming[r]) if edge[0] not in (q,r)]
        excluded={q,r}
        def good(edge,mutT):
            p,b=edge
            for pat in pats[edge]:
                a=oldtrails[edge][pat]
                actual=trail(p,pat,k,limit,mutT)
                if not any(z[0] not in excluded and z in a for z in actual):return False
            return True
        if allpairs and not all(good(edge,newT) for edge in incoming[q] if edge[0] not in (q,r)):continue
        bad=[edge for edge in checks if not good(edge,newT)]
        if len(bad)>3:continue
        edits={}
        for edge in bad:
            orig=newT[edge];opts=[]
            for w,d in [(orig[0],orig[1]),(orig[0],-orig[1]),(1-orig[0],orig[1]),(1-orig[0],-orig[1])]:
                for s in Q:
                    if s==q:continue
                    newT[edge]=(w,d,s)
                    if good(edge,newT):opts.append((w,d,s))
                if opts:break
            newT[edge]=orig
            if not opts:break
            edits[edge]=opts
        if len(edits)!=len(bad):continue
        for choices in product(*(edits[e] for e in bad)):
            for e,val in zip(bad,choices):newT[e]=val
            if all(good(e,newT) for e in checks):
                patch={str(e):v for e,v in newT.items() if T[e]!=v}
                sol={'deleted':q,'absorber':r,'patch':patch,'excluded':sorted(excluded),'checks':[list(e) for e in checks]}
                print('SOLUTION',sol,flush=True);solutions.append(sol)
                break
    (BASE/f'compensation_search{k}.json').write_text(json.dumps(solutions,indent=2))
    print('done',len(solutions),'elapsed',round(time.time()-start,2))

if __name__=='__main__':search(int(sys.argv[1]) if len(sys.argv)>1 else 4)
