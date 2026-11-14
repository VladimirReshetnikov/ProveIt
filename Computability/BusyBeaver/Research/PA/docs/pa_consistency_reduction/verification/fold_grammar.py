#!/usr/bin/env python3
"""Find predecessor-bit reader folds of a newly compiled AX grammar."""
import symbolic as S
from pathlib import Path
import sys,json,itertools,time
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'reduction196'))
from site_contexts import words

def freeze(x):return tuple(map(freeze,x)) if isinstance(x,list) else x

def contexts(m,r=2):
    ctx={q:set() for q,b in m if all(m[q,b][:2]==(b,1) for b in [0,1])}
    info,obs=S.verify(m,collect=True)
    for i,branch,trace in obs:
        for kind,s,row in trace:
            if kind!='step' or s[0] not in ctx:continue
            q,onl,l,rs=s
            for left in words(l,r,True):
                for right in words(rs,r+1):
                    v=left[::-1]+right
                    ctx[q].add(sum(x<<i for i,x in enumerate(v)))
    return ctx

def candidates(m,ctx,r=2):
    tags={}
    for q,ts in ctx.items():
        for b in [0,1]:
            s={(t>>(r-1))&1 for t in ts if (t>>r)&1==b}
            if len(s)==1:tags[q,b]=next(iter(s))
    pure=list(ctx)
    protected={q for q,b in S.ENGINE_ROWS}|{m[k][2] for k in S.ENGINE_ROWS}|{0,S.ROOT}
    for q,p in itertools.combinations([q for q in pure if q not in protected],2):
        alternatives=[]
        for b in [0,1]:
            if m[q,b]==m[p,b]:alternatives.append([m[q,b]]);continue
            if (q,b) not in tags or (p,b)not in tags or tags[q,b]==tags[p,b]:break
            z=[]
            for h in pure:
                if h in (q,p):continue
                a=m[h,tags[q,b]][2];c=m[h,tags[p,b]][2]
                if a in(q,p)or c in(q,p):continue
                if m.get((a,b))==m[q,b] and m.get((c,b))==m[p,b]:z.append((b,-1,h))
            if not z:break
            alternatives.append(z)
        else:
            for row0,row1 in itertools.product(*alternatives):yield q,p,row0,row1

def folded(m,change):
    q,p,a0,a1=change
    nm=m|{(q,0):a0,(q,1):a1}
    return {k:(w,d,q if s==p else s)for k,(w,d,s)in nm.items()if k[0]!=p}

def main():
    name=sys.argv[1] if len(sys.argv)>1 else 'safe_guard'
    d=Path(__file__).with_name('compiled')
    tree=freeze(json.loads((d/(name+'.json')).read_text())['tree'])
    sites=S.flatten(tree);S.all_sites=lambda:sites
    m=S.load_machine(d/(name+'.tm'));changes=[]
    for rnd in range(20):
        ctx=contexts(m);opts=list(candidates(m,ctx))
        print('ROUND',rnd,'states',len(m)//2,'candidates',len(opts),opts[:20],flush=True)
        success=False
        # Prefer folds entirely within the regenerated body.
        opts.sort(key=lambda x:(x[0]<1000 or x[1]<1000,x[0],x[1]))
        for ch in opts:
            nm=folded(m,ch)
            try:info,_=S.verify(nm)
            except Exception as e:print('failed',ch,str(e),flush=True);continue
            print('SUCCESS',ch,info,flush=True);m=nm;changes.append(ch);success=True
            (d/(name+'_folded.tm')).write_text(''.join(f'{q} {b} {w} {"R" if dr==1 else "L"} {n}\n' for(q,b),(w,dr,n)in sorted(m.items())))
            (d/(name+'_folds.json')).write_text(json.dumps(changes,indent=2))
            break
        if not success:break
    print('DONE',len(m)//2,changes,flush=True)

if __name__=='__main__':main()
