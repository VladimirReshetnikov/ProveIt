"""Exact local-control reassociation search; source-only until compiled.

Each node signature records every ordered instruction and its two possible
control targets.  External break/continue targets retain the number of
ancestors still needed.  Equality therefore is valid in every surrounding
source context, without a syntactic closedness assumption.
"""
from pathlib import Path
from functools import cache
import json,sys,time,random

HERE=Path(__file__).resolve().parent
J=json.loads((HERE/'boundary_source_input.json').read_text())
S=[tuple(x) for x in J['structures']]
I={x:i for i,x in enumerate(S)}
ROOT=J['root']; N0=len(S)

def cons(a,b):
    pair=(a,b)
    if pair not in I:I[pair]=len(S);S.append(pair)
    return I[pair]

@cache
def paths(n):
    x=S[n]
    if isinstance(x[0],str):return (('',x[0],x[1]),)
    return tuple((str(b)+p,o,r) for b in (0,1) for p,o,r in paths(x[b]))

def signature_by_paths(n):
    pp=paths(n); count=len(pp); intervals={}
    for i,(p,o,r) in enumerate(pp):
        for k in range(len(p)+1):
            s=p[:k]
            if s not in intervals:intervals[s]=[i,i+1]
            else:intervals[s][1]=i+1
    def brk(p,k):
        cuts=[i for i,b in enumerate(p) if b=='0']
        if len(cuts)<k:return ('break',k-len(cuts))
        dst=intervals[p[:cuts[-k]]][1]
        return dst if dst<count else ('break',0)
    def cont(p,k):
        cuts=[i for i,b in enumerate(p) if b=='1']
        if len(cuts)<k:return ('continue',k-len(cuts))
        return intervals[p[:cuts[-k]]][0]
    out=[]
    for i,(p,o,r) in enumerate(pp):
        normal=i+1 if i+1<count else ('break',0)
        dest=(normal,) if o=='CI' else (brk(p,1),normal) if o=='CD' else (brk(p,r),) if o=='CB' else (cont(p,r),) if o=='CC' else ('halt',)
        out.append((o,r,dest))
    return tuple(out)

@cache
def signature(n):
    """Compositional calculation, checked against the path-based definition."""
    x=S[n]
    if isinstance(x[0],str):
        o,r=x
        dest=(('break',0),) if o=='CI' else (('break',1),('break',0)) if o=='CD' else (('break',r),) if o=='CB' else (('continue',r),) if o=='CC' else ('halt',)
        return ((o,r,dest),)
    a,b=map(signature,x);offset=len(a)
    def lt(t):
        if not isinstance(t,tuple):return t
        k,v=t
        return (offset if v==0 else ('break',v-1)) if k=='break' else t
    def rt(t):
        if isinstance(t,int):return t+offset
        if not isinstance(t,tuple):return t
        k,v=t
        return (0 if v==1 else ('continue',v-1)) if k=='continue' else t
    return tuple((o,r,tuple(map(lt,dd))) for o,r,dd in a)+tuple((o,r,tuple(map(rt,dd))) for o,r,dd in b)

@cache
def boundary(n):
    x=S[n]
    if isinstance(x[0],str):return (1,0,False) if x[0]=='CD' else (x[1],0,False) if x[0]=='CB' else (0,x[1],False) if x[0]=='CC' else (0,0,x[0]=='CH')
    a,b=map(boundary,x)
    return (max(max(a[0]-1,0),b[0]),max(a[1],max(b[1]-1,0)),a[2] or b[2])

def closed(n):return boundary(n)==(0,0,False)

@cache
def live(n):
    if isinstance(S[n][0],str):return frozenset([n])
    return frozenset([n])|live(S[n][0])|live(S[n][1])

@cache
def lead(n):return 1+lead(S[n][0]) if isinstance(S[n][0],int) else 0
@cache
def zero_run(n):return max(1+lead(S[n][0]),zero_run(S[n][0]),zero_run(S[n][1])) if isinstance(S[n][0],int) else 0
@cache
def depth(n):return 1+max(depth(S[n][0]),depth(S[n][1])) if isinstance(S[n][0],int) else 0

def score(n):return len(live(n)),zero_run(n),depth(n)

def replace(root,n,alt):
    @cache
    def f(k):
        if k==n:return alt
        if isinstance(S[k][0],str):return k
        return cons(*map(f,S[k]))
    return f(root)

@cache
def rotations(n):
    x=S[n];out=[]
    if isinstance(x[0],str):return tuple(out)
    a,b=x
    if isinstance(S[b][0],int):
        b,c=S[b]; alt=cons(cons(a,b),c)
        if boundary(a)[0]==0 and boundary(c)[1]==0:out.append((alt,'L',(a,b,c),all(map(closed,(a,b,c)))))
    a,c=x
    if isinstance(S[a][0],int):
        a,b=S[a]; alt=cons(a,cons(b,c))
        if boundary(a)[0]==0 and boundary(c)[1]==0:out.append((alt,'R',(a,b,c),all(map(closed,(a,b,c)))))
    return tuple(out)

def export(root,hist,name,extra=None):
    keep=set(range(N0))|set(live(root))
    for m in hist:
        for n in [m['node'],m['alternative'],*m['chunks']]:keep.update(live(n))
    mp={old:i for i,old in enumerate(sorted(keep))}
    data=dict(status='SOURCE_ONLY',original_root=ROOT,root=mp[root],structures=[tuple(mp[a] for a in S[n]) if isinstance(S[n][0],int) else S[n] for n in sorted(keep)],history=[dict(m,node=mp[m['node']],alternative=mp[m['alternative']],chunks=[mp[a] for a in m['chunks']]) for m in hist],score=score(root),sites=paths(root))
    if extra:data.update(extra)
    (HERE/name).write_text(json.dumps(data,indent=2)+'\n')

def compact(beam):
    keep=set(range(N0))
    for root,hist in beam:
        keep.update(live(root))
        for m in hist:
            for n in [m['node'],m['alternative'],*m['chunks']]:keep.update(live(n))
    mp={old:i for i,old in enumerate(sorted(keep))}
    new=[tuple(mp[a] for a in S[n]) if isinstance(S[n][0],int) else S[n] for n in sorted(keep)]
    out=[(mp[r],[dict(m,node=mp[m['node']],alternative=mp[m['alternative']],chunks=[mp[a] for a in m['chunks']]) for m in h]) for r,h in beam]
    S[:]=new;I.clear();I.update({x:i for i,x in enumerate(S)})
    for f in (paths,signature,boundary,live,lead,zero_run,depth,rotations):f.cache_clear()
    return out

def main():
    width=int(sys.argv[1]) if len(sys.argv)>1 else 80
    levels=int(sys.argv[2]) if len(sys.argv)>2 else 10
    cap=int(sys.argv[3]) if len(sys.argv)>3 else 224
    beam=[(ROOT,[])];seen={ROOT};began=time.time();stats=[];best=score(ROOT)
    for n in live(ROOT):assert signature(n)==signature_by_paths(n),n
    for n in live(ROOT):
        for alt,*_ in rotations(n):assert signature(n)==signature(alt),(n,alt)
    paths.cache_clear();signature.cache_clear()
    print('BASE',best,'nodes',len(S),flush=True)
    for level in range(levels):
        new=[];examined=0;extra=0;accepted=0
        for root,hist in beam:
            for n in sorted(live(root)):
                for alt,d,chunks,allclosed in rotations(n):
                    nr=replace(root,n,alt)
                    if nr in seen:continue
                    seen.add(nr);examined+=1;extra+=not allclosed
                    sc=score(nr)
                    if sc[0]>cap or sc[1]>6:continue
                    accepted+=1
                    nh=hist+[dict(node=n,alternative=alt,direction=d,chunks=chunks,all_closed=allclosed)]
                    if sc<best:
                        best=sc;export(nr,nh,'best_source.json')
                        print('BEST',sc,'history',nh,flush=True)
                    if sc[0]<224:
                        export(nr,nh,'source223_found.json');print('FOUND',sc,flush=True);return
                    new.append((sc,nr,nh))
        new.sort(key=lambda item:(item[0],item[1]))
        beam=[(nr,nh) for sc,nr,nh in new[:width]]
        row=dict(level=level+1,examined=examined,beyond_closed=extra,accepted=accepted,beam=len(beam),seconds=round(time.time()-began,3),best=best)
        stats.append(row);print(row,flush=True)
        (HERE/'search_stats.json').write_text(json.dumps(dict(status='BOUNDED_SEARCH',width=width,levels=levels,cap=cap,stats=stats),indent=2)+'\n')
        if not beam:break
        beam=compact(beam);seen={r for r,h in beam}
    (HERE/'search_stats.json').write_text(json.dumps(dict(status='BOUNDED_SEARCH_COMPLETE_NO_NODE_REDUCTION',width=width,levels=levels,cap=cap,total_generated_alternatives=sum(x['examined'] for x in stats),generated_beyond_all_closed_rule=sum(x['beyond_closed'] for x in stats),accepted_alternatives=sum(x['accepted'] for x in stats),best=best,stats=stats),indent=2)+'\n')

if __name__=='__main__':main()
