from pathlib import Path
import json,sys,itertools,collections,time
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'verification'))
import symbolic as S
from search_merges import load

def candidates(m,ctx,r=4):
    qs=list(ctx);bit={}
    for q in qs:
        for b in (0,1):
            a={(x>>(r-1))&1 for x in ctx[q] if (x>>r)&1==b}
            if len(a)==1:bit[q,b]=next(iter(a))
    h=collections.defaultdict(set)
    for q,p in itertools.combinations(qs,2):
        diff=[b for b in (0,1) if m[q,b]!=m[p,b]]
        if len(diff)!=1:continue
        b=diff[0]
        if (q,b) not in bit or (p,b) not in bit or bit[q,b]==bit[p,b]:continue
        if bit[q,b]:q,p=p,q
        aa=[s for s in qs if m[s,b]==m[q,b] and s not in(q,p)]
        bb=[s for s in qs if m[s,b]==m[p,b] and s not in(q,p)]
        for s,t in itertools.product(aa,bb):h[s,t].add((q,p,b))
    return h

def edit(m,helper,merges):
    a,b=helper
    mapping={p:q for q,p,r in merges}
    n=m.copy()
    n[500,0]=(0,1,a);n[500,1]=(1,1,b)
    for q,p,r in merges:
        n[q,r]=(r,-1,500)
        del n[p,0];del n[p,1]
    return {(q,r):(w,d,mapping.get(t,t)) for (q,r),(w,d,t) in n.items()}

if __name__=='__main__':
    start=time.time();m=S.load_machine()
    ctx={int(q):v for q,v in json.loads(Path(__file__).with_name('site_contexts.json').read_text()).items()}
    h=candidates(m,ctx)
    contracts=S.contracts();n=0
    for helper,pairs in h.items():
        for p1,p2 in itertools.combinations(pairs,2):
            if len(set(p1[:2]+p2[:2]))<4 or any(x in helper for x in p1[:2]+p2[:2]):continue
            n+=1;new=edit(m,helper,[p1,p2])
            if not S.check_engine(new):continue
            ok=True
            for i,branch,br,s,t in contracts:
                if S.execute(new,br,s,t) is None:ok=False;break
            if ok:
                result={'helper':helper,'merges':[p1,p2]}
                print('SUCCESS',result,flush=True)
                Path(__file__).with_name('shared_success.json').write_text(json.dumps(result))
                Path(__file__).with_name('pa195_raw.tm').write_text(''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {t}\n' for (q,b),(w,d,t) in sorted(new.items())))
                break
        else:continue
        break
    print('candidates',n,'helperpairs',len(h),'seconds',time.time()-start)
