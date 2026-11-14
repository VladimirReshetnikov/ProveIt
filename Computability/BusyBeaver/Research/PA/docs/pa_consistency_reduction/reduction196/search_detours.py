from search_merges import load,contexts
from pathlib import Path
from itertools import combinations
import sys,json,time

def tryroute(m,patterns,r,b,s,target,direction='L',bound=15,write=None):
    visited=set(); lengths=set()
    for old in patterns:
        x=r+(-1 if direction=='L' else 1);q=s;t=old if write is None else (old&~(1<<r))|(write<<r)
        for k in range(1,bound+1):
            if x==r+1 and q==target and t==old:
                lengths.add(k);break
            if x<0 or x>2*r or (q,(t>>x)&1) not in m:return
            visited.add(q)
            v=(t>>x)&1;w,d,q=m[q,v]
            t=(t&~(1<<x))|(w<<x);x+=1 if d=='R' else -1
        else:return
    return visited,lengths

def search(m,r=4,bound=15,ctx=None):
    qs=sorted(set(q for q,b in m)); ctx=contexts(m,r) if ctx is None else ctx
    pure=[q for q in qs if all(m[q,b][:2]==(b,'R') for b in range(2))]
    opts={}
    for q in pure:
        for b in range(2):
            pat=[t for t in ctx[q] if (t>>r)&1==b]
            cand={(b,'R',m[q,b][2]):(set(),{1})}
            for s in qs:
                if s==q:continue
                for d in ('L','R'):
                    for w in (0,1):
                        v=tryroute(m,pat,r,b,s,m[q,b][2],d,bound,w)
                        if v is not None and q not in v[0]:cand[w,d,s]=v
            opts[q,b]=cand
    out=[]
    for q,p in combinations(pure,2):
        cs=[]
        for b in range(2):
            z={}
            for a in set(opts[q,b])&set(opts[p,b]):
                vis=opts[q,b][a][0]|opts[p,b][a][0]
                if p not in vis and q not in vis and a[2] not in (p,q):
                    z[str(a)]={'q_lengths':sorted(opts[q,b][a][1]),'r_lengths':sorted(opts[p,b][a][1]),'visited':sorted(vis)}
            cs.append(z)
        if all(cs):out.append({'q':q,'r':p,'options':cs})
    return out

if __name__=='__main__':
    t=time.time();r=int(sys.argv[1]) if len(sys.argv)>1 else 4
    m=load(Path(__file__).with_name('pa196.tm'))
    cache=Path(__file__).with_name('site_contexts.json')
    ctx={int(q):set(v) for q,v in json.loads(cache.read_text()).items()} if len(sys.argv)>2 and sys.argv[2]=='sites' else None
    ans=search(m,r,ctx=ctx)
    print(json.dumps(ans,indent=2));print('Seconds:',time.time()-t)
