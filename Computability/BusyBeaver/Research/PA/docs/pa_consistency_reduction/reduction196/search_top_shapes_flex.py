from search_top_shapes import *

def adapt(sites,old):
    starts={}
    for i,(p,op) in enumerate(sites):
        for j in range(len(p)+1):starts.setdefault(p[:j],i)
    def find(p):
        if p is None:return 0
        if p in starts:return starts[p]
        while p and p[-1]==0:
            p=p[:-1]
            if p in starts:return starts[p]
        raise ValueError
    out=[];changes=[]
    for i,(p,op)in enumerate(sites):
        typ=op[0]
        if typ=='inc':z=('inc',op[1],find(S.successor(p)))
        elif typ=='dec':
            try:z=('dec',op[1],find(S.successor(S.cut(p,0,1))),find(S.successor(p)))
            except ValueError:return
        elif typ=='halt':z=('halt',)
        else:
            opts=[]
            for k in(1,2,3):
                for ty in('breakTo','continueTo'):
                    try:
                        dst=find(S.successor(S.cut(p,0,k)))if ty=='breakTo'else find(S.cut(p,1,k))
                        if ('jump',dst)==old[i]:opts.append((ty,k))
                    except ValueError:pass
            if not opts:return
            z=old[i]
            if op not in opts:op=opts[0];changes.append((i,op))
        if z!=old[i]:return
        out.append((p,op))
    return out,changes

def rebuild(sites):
    d={p:('leaf',op)for p,op in sites}
    for p in sorted({p[:i]for p,o in sites for i in range(len(p))},key=len,reverse=True):d[p]=(d[p+(0,)],d[p+(1,)])
    return d[()]

if __name__=='__main__':
    t,n=S.source_tree();old=fastcodes(S.flatten(t))
    keys=['dec5','node1','dec6','node5','halt','node20','node170','node23']
    special={'dec5':('leaf',('dec',5)),'dec6':('leaf',('dec',6)),'halt':('leaf',('halt',))}
    leaves=[n[k]if k in n else special[k]for k in keys]
    out=[]
    for sh in shapes(0,len(leaves)):
        if len(leafdepth(sh,0))>5:continue
        nt=expand(sh,leaves);ss=S.flatten(nt)
        z=adapt(ss,old)
        if z is None:continue
        ns,changes=z;nt=rebuild(ns)
        count=len(nodes(nt));viol=sum('000000'in''.join(map(str,p))for p,o in ns)
        keep=leafdepth(sh,5).endswith('1')
        out.append((sh,count,viol,keep,[leafdepth(sh,i)for i in range(len(leaves))],changes))
    for r in sorted(out,key=lambda x:(x[2],not x[3],x[1]))[:60]:print(r)
    print('valid',len(out))
    Path(__file__).with_name('top_shapes_flex.json').write_text(json.dumps(out))
