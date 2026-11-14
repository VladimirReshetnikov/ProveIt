from pathlib import Path
import sys,itertools,functools,json,collections
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'verification'))
import symbolic as S

def fastcodes(sites):
    starts={}
    for i,(p,op) in enumerate(sites):
        for j in range(len(p)+1):starts.setdefault(p[:j],i)
    def find(p):
        if p is None:return 0
        if p in starts:return starts[p]
        while p and p[-1]==0:
            p=p[:-1]
            if p in starts:return starts[p]
        raise ValueError('bad path')
    out=[]
    for p,op in sites:
        tag=op[0]
        if tag=='inc':out.append(('inc',op[1],find(S.successor(p))))
        elif tag=='dec':out.append(('dec',op[1],find(S.successor(S.cut(p,0,1))),find(S.successor(p))))
        elif tag=='breakTo':out.append(('jump',find(S.successor(S.cut(p,0,op[1])))))
        elif tag=='continueTo':out.append(('jump',find(S.cut(p,1,op[1]))))
        else:out.append(('halt',))
    return out

@functools.lru_cache(None)
def shapes(a,b):
    if b-a==1:return (a,)
    return tuple((l,r)for i in range(a+1,b)for l in shapes(a,i)for r in shapes(i,b))

def expand(s,leaves):return leaves[s] if isinstance(s,int)else(expand(s[0],leaves),expand(s[1],leaves))
def leafdepth(s,i,p=''):
    if isinstance(s,int):return p if s==i else None
    return leafdepth(s[0],i,p+'0') or leafdepth(s[1],i,p+'1')

def nodes(t):return set()if t[0]=='leaf'else{t}|nodes(t[0])|nodes(t[1])

if __name__=='__main__':
    t,n=S.source_tree();old=fastcodes(S.flatten(t));assert old==S.instructions(S.flatten(t))
    nm=json.loads((Path(__file__).resolve().parents[1]/'verification/node_map.json').read_text())
    # Expand just the leftmost control skeleton. All leaves are existing subprograms.
    keys=['node2','dec6','node5','halt','node20','node170','node23']
    leaves=[n.get(k,('leaf',('dec',6))if k=='dec6'else('leaf',('halt',)))for k in keys]
    out=[]
    for sh in shapes(0,len(leaves)):
        if len(leafdepth(sh,0))>4:continue
        nt=expand(sh,leaves)
        try:nc=fastcodes(S.flatten(nt))
        except ValueError:continue
        if nc!=old:continue
        count=len(nodes(nt));viol=sum('000000'in''.join(map(str,p))for p,o in S.flatten(nt))
        keep=leafdepth(sh,4).endswith('1')
        out.append((sh,count,viol,keep,[leafdepth(sh,i)for i in range(len(leaves))]))
    for r in sorted(out,key=lambda x:(x[2],not x[3],x[1])):print(r)
    print('valid',len(out))
    Path(__file__).with_name('top_shapes.json').write_text(json.dumps(out))
