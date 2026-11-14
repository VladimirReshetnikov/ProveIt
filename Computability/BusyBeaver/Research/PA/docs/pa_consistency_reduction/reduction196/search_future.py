"""State merges allowing local detours to rejoin a later original configuration."""
from pathlib import Path
import json,sys,itertools,time
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'verification'))
import symbolic as S

def old_futures(m,patterns,r,q,bound=8):
    futures={}
    for orig in patterns:
        s=q;x=r;t=orig;targets=set()
        for k in range(bound):
            if x<0 or x>2*r or (s,(t>>x)&1) not in m:break
            w,d,s=m[s,(t>>x)&1];t=(t&~(1<<x))|(w<<x);x+=d
            cf=(s,x,t)
            if cf in targets:break
            targets.add(cf)
        futures[orig]=targets
    return futures

def route(m,futures,r,q,a,bound=25):
    w,d,state=a;visited=set();lengths=set()
    for orig,targets in futures.items():
        x=r+d;t=(orig&~(1<<r))|(w<<r);s=state;seen=set()
        for k in range(1,bound+1):
            if (s,x,t) in targets:lengths.add(k);break
            cf=(s,x,t)
            if x<0 or x>2*r or s==q or (s,(t>>x)&1) not in m or cf in seen:return
            seen.add(cf);visited.add(s)
            v=(t>>x)&1;ww,dd,s=m[s,v]
            t=(t&~(1<<x))|(ww<<x);x+=dd
        else:return
    return visited,lengths

def candidates(m,ctx,r=4,oldbound=8,newbound=25):
    qs=sorted(ctx);protected={q for q,b in S.ENGINE_ROWS}|{0,S.ROOT}
    can=[q for q in qs if q not in protected];opts={}
    for qi,q in enumerate(can):
        for b in (0,1):
            pat=[t for t in ctx[q] if (t>>r)&1==b]
            if not pat:opts[q,b]={m[q,b]:(set(),{1})};continue
            futures=old_futures(m,pat,r,q,oldbound)
            v={m[q,b]:(set(),{1})}
            for s in qs:
                if s==q:continue
                for d in (-1,1):
                    for w in (0,1):
                        a=(w,d,s);k=route(m,futures,r,q,a,newbound)
                        if k is not None:v[a]=k
            opts[q,b]=v
    out=[]
    for q,p in itertools.combinations(can,2):
        lists=[]
        for b in (0,1):
            good=[]
            for a in set(opts[q,b])&set(opts[p,b]):
                if a[2] in(q,p):continue
                vis=opts[q,b][a][0]|opts[p,b][a][0]
                if q in vis or p in vis:continue
                good.append(a)
            lists.append(good)
        for a0,a1 in itertools.product(*lists):out.append((q,p,a0,a1))
    return out

if __name__=='__main__':
    from site_contexts import contexts
    root=Path(__file__).resolve().parents[1]
    variant=sys.argv[1]if len(sys.argv)>1 else'original'
    if variant=='original':
        m=S.load_machine();sites=S.all_sites()
    elif variant=='h':
        base=root/'comparison/audit/h_catalan_node170_3_133_37'
        m=S.load_machine(str(base)+'.tm')
        sites=[(tuple(p),tuple(o))for p,o in json.loads(Path(str(base)+'_sites.json').read_text())]
    else:
        base=root/'verification/candidates/open_physical_61_201240_safe'
        m=S.load_machine(str(base)+'.tm')
        def tuples(v):return tuple(map(tuples,v))if isinstance(v,list)else v
        sites=S.flatten(tuples(json.loads(Path(str(base)+'.json').read_text())['tree']))
    S.all_sites=lambda:sites
    start=time.time();ctx=contexts(4,True,m)
    c=candidates(m,ctx)
    print('Candidates',variant,len(c),c,flush=True)
    for q,p,a0,a1 in c:
        n=m.copy();n[q,0]=a0;n[q,1]=a1;del n[p,0];del n[p,1]
        n={k:(w,d,q if s==p else s) for k,(w,d,s) in n.items()}
        try:totals,_=S.verify(n)
        except Exception as e:print('failed',q,p,str(e),flush=True);continue
        print('SUCCESS',q,p,a0,a1,totals,flush=True)
        Path(__file__).with_name(f'future_{variant}_success.json').write_text(json.dumps((q,p,a0,a1)))
        Path(__file__).with_name(f'future_{variant}_success.tm').write_text(''.join(f'{qq} {bb} {w} {"R" if d==1 else "L"} {t}\n' for (qq,bb),(w,d,t) in sorted(n.items())))
    print('seconds',time.time()-start)
