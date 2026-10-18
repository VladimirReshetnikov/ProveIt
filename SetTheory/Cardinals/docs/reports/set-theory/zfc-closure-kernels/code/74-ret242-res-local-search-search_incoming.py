from search_folds import *
import time

def main(k=4,limit=14):
    cached=BASE/f'windows{k}.json'
    seen={int(q):set(ps) for q,ps in json.loads(cached.read_text()).items()} if cached.exists() else reachable_windows(k)
    trails={q:{p:set(trail(q,p,k,limit)) for p in seen[q]} for q in Q}
    incoming=defaultdict(list)
    for edge,(_,_,q) in T.items():incoming[q].append(edge)
    proofs={}
    start=time.time()
    for q in Q:
        if q==95 or any(p==q for p,b in incoming[q]):continue
        viable=True; replacements={}
        for p,b in incoming[q]:
            opts=[]
            patterns=[pat for pat in seen[p] if (pat>>k)&1==b]
            old=T[p,b]
            newT={key:val for key,val in T.items() if key[0]!=q}
            for d in [old[1],-old[1]]:
                for w in [old[0],1-old[0]]:
                    for r in Q:
                        if r==q:continue
                        newT[p,b]=(w,d,r)
                        ok=True
                        for pat in patterns:
                            targets=trails[p][pat]
                            actual=trail(p,pat,k,limit,newT)
                            if not any(a[0]!=q and a in targets for a in actual):
                                ok=False;break
                        if ok:opts.append((w,d,r))
            replacements[p,b]=opts
            if not opts:
                viable=False;break
        if viable:
            print('VIABLE',q,replacements,flush=True)
            proofs[q]={str(key):v for key,v in replacements.items()}
    (BASE/f'incoming_search{k}.json').write_text(json.dumps(proofs,indent=2))
    print('elapsed',time.time()-start)

if __name__=='__main__':main(int(sys.argv[1]) if len(sys.argv)>1 else 4)
