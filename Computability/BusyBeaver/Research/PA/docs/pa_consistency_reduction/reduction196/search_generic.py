from pathlib import Path
import json,sys,itertools,time,ast
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'verification'))
import symbolic as S

def route(m,patterns,r,b,q,a,bound=21):
    oldw,oldd,target=m[q,b];w,d,state=a
    visited=set();lengths=set()
    for orig in patterns:
        x=r+d;t=(orig&~(1<<r))|(w<<r);s=state
        final=(orig&~(1<<r))|(oldw<<r)
        for k in range(1,bound+1):
            if x==r+oldd and s==target and t==final:lengths.add(k);break
            if x<0 or x>2*r or s==q or (s,(t>>x)&1) not in m:return
            visited.add(s)
            v=(t>>x)&1;ww,dd,s=m[s,v]
            t=(t&~(1<<x))|(ww<<x);x+=dd
        else:return
    return visited,lengths

def candidates(m,ctx,r=4):
    qs=sorted(ctx);protected={q for q,b in S.ENGINE_ROWS}|{0,S.ROOT}
    can=[q for q in qs if q not in protected]
    opts={}
    for q in can:
        for b in (0,1):
            pat=[t for t in ctx[q] if (t>>r)&1==b]
            if not pat:opts[q,b]={m[q,b]:(set(),{1})};continue
            v={m[q,b]:(set(),{1})}
            for s in qs:
                if s==q:continue
                for d in (-1,1):
                    for w in (0,1):
                        a=(w,d,s)
                        k=route(m,pat,r,b,q,a)
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
    start=time.time();m=S.load_machine()
    ctx={int(q):v for q,v in json.loads(Path(__file__).with_name('site_contexts.json').read_text()).items()}
    c=candidates(m,ctx)
    print('Candidates',c,flush=True)
    for q,p,a0,a1 in c:
        n=m.copy();n[q,0]=a0;n[q,1]=a1;del n[p,0];del n[p,1]
        n={k:(w,d,q if s==p else s) for k,(w,d,s) in n.items()}
        try:
            totals,_=S.verify(n)
        except Exception as e:print('failed',q,p,str(e),flush=True);continue
        print('SUCCESS',q,p,a0,a1,totals,flush=True)
        Path(__file__).with_name('generic_success.json').write_text(json.dumps((q,p,a0,a1)))
        Path(__file__).with_name('pa195_raw.tm').write_text(''.join(f'{qq} {bb} {w} {"R" if d==1 else "L"} {t}\n' for (qq,bb),(w,d,t) in sorted(n.items())))
    print('seconds',time.time()-start)
